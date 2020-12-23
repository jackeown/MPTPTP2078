%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:47 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 146 expanded)
%              Number of leaves         :   22 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :  118 ( 506 expanded)
%              Number of equality atoms :   21 ( 126 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( B = k2_funct_1(A)
            <=> ( k1_relat_1(B) = k2_relat_1(A)
                & ! [C,D] :
                    ( ( ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) )
                     => ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) ) )
                    & ( ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) )
                     => ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_38,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_99,plain,(
    ! [A_37,C_38] :
      ( k1_funct_1(A_37,k1_funct_1(k2_funct_1(A_37),C_38)) = C_38
      | ~ r2_hidden(C_38,k2_relat_1(A_37))
      | ~ v1_funct_1(k2_funct_1(A_37))
      | ~ v1_relat_1(k2_funct_1(A_37))
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5'
    | k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_47,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_119,plain,
    ( ~ r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_47])).

tff(c_134,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_119])).

tff(c_137,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_140,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_137])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_140])).

tff(c_145,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_149,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_145])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_149])).

tff(c_155,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_160,plain,(
    ! [A_39] :
      ( k1_relat_1(k2_funct_1(A_39)) = k2_relat_1(A_39)
      | ~ v1_funct_1(k2_funct_1(A_39))
      | ~ v1_relat_1(k2_funct_1(A_39))
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_165,plain,(
    ! [A_40] :
      ( k1_relat_1(k2_funct_1(A_40)) = k2_relat_1(A_40)
      | ~ v1_funct_1(k2_funct_1(A_40))
      | ~ v2_funct_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(resolution,[status(thm)],[c_4,c_160])).

tff(c_169,plain,(
    ! [A_1] :
      ( k1_relat_1(k2_funct_1(A_1)) = k2_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_165])).

tff(c_185,plain,(
    ! [B_44,C_45,A_46] :
      ( k1_funct_1(k5_relat_1(B_44,C_45),A_46) = k1_funct_1(C_45,k1_funct_1(B_44,A_46))
      | ~ r2_hidden(A_46,k1_relat_1(B_44))
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45)
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_297,plain,(
    ! [A_59,C_60,A_61] :
      ( k1_funct_1(k5_relat_1(k2_funct_1(A_59),C_60),A_61) = k1_funct_1(C_60,k1_funct_1(k2_funct_1(A_59),A_61))
      | ~ r2_hidden(A_61,k2_relat_1(A_59))
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60)
      | ~ v1_funct_1(k2_funct_1(A_59))
      | ~ v1_relat_1(k2_funct_1(A_59))
      | ~ v2_funct_1(A_59)
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_185])).

tff(c_154,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_317,plain,
    ( k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5'
    | ~ r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_154])).

tff(c_331,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_44,c_42,c_38,c_155,c_317])).

tff(c_333,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_405,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_333])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_405])).

tff(c_410,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_414,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_410])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:21:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.52  
% 2.99/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.52  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 2.99/1.52  
% 2.99/1.52  %Foreground sorts:
% 2.99/1.52  
% 2.99/1.52  
% 2.99/1.52  %Background operators:
% 2.99/1.52  
% 2.99/1.52  
% 2.99/1.52  %Foreground operators:
% 2.99/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.99/1.52  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.99/1.52  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.99/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.99/1.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.99/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.99/1.52  tff('#skF_5', type, '#skF_5': $i).
% 2.99/1.52  tff('#skF_6', type, '#skF_6': $i).
% 2.99/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.99/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.99/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.99/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.99/1.52  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.99/1.52  
% 3.05/1.54  tff(f_91, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 3.05/1.54  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.05/1.54  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_funct_1)).
% 3.05/1.54  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 3.05/1.54  tff(c_44, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.05/1.54  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.05/1.54  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.05/1.54  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.05/1.54  tff(c_40, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.05/1.54  tff(c_38, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.05/1.54  tff(c_99, plain, (![A_37, C_38]: (k1_funct_1(A_37, k1_funct_1(k2_funct_1(A_37), C_38))=C_38 | ~r2_hidden(C_38, k2_relat_1(A_37)) | ~v1_funct_1(k2_funct_1(A_37)) | ~v1_relat_1(k2_funct_1(A_37)) | ~v2_funct_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.05/1.54  tff(c_36, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5' | k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.05/1.54  tff(c_47, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_36])).
% 3.05/1.54  tff(c_119, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_99, c_47])).
% 3.05/1.54  tff(c_134, plain, (~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_119])).
% 3.05/1.54  tff(c_137, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_134])).
% 3.05/1.54  tff(c_140, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_137])).
% 3.05/1.54  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_140])).
% 3.05/1.54  tff(c_145, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_134])).
% 3.05/1.54  tff(c_149, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_145])).
% 3.05/1.54  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_149])).
% 3.05/1.54  tff(c_155, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_36])).
% 3.05/1.54  tff(c_160, plain, (![A_39]: (k1_relat_1(k2_funct_1(A_39))=k2_relat_1(A_39) | ~v1_funct_1(k2_funct_1(A_39)) | ~v1_relat_1(k2_funct_1(A_39)) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.05/1.54  tff(c_165, plain, (![A_40]: (k1_relat_1(k2_funct_1(A_40))=k2_relat_1(A_40) | ~v1_funct_1(k2_funct_1(A_40)) | ~v2_funct_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(resolution, [status(thm)], [c_4, c_160])).
% 3.05/1.54  tff(c_169, plain, (![A_1]: (k1_relat_1(k2_funct_1(A_1))=k2_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_2, c_165])).
% 3.05/1.54  tff(c_185, plain, (![B_44, C_45, A_46]: (k1_funct_1(k5_relat_1(B_44, C_45), A_46)=k1_funct_1(C_45, k1_funct_1(B_44, A_46)) | ~r2_hidden(A_46, k1_relat_1(B_44)) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.05/1.54  tff(c_297, plain, (![A_59, C_60, A_61]: (k1_funct_1(k5_relat_1(k2_funct_1(A_59), C_60), A_61)=k1_funct_1(C_60, k1_funct_1(k2_funct_1(A_59), A_61)) | ~r2_hidden(A_61, k2_relat_1(A_59)) | ~v1_funct_1(C_60) | ~v1_relat_1(C_60) | ~v1_funct_1(k2_funct_1(A_59)) | ~v1_relat_1(k2_funct_1(A_59)) | ~v2_funct_1(A_59) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(superposition, [status(thm), theory('equality')], [c_169, c_185])).
% 3.05/1.54  tff(c_154, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_36])).
% 3.05/1.54  tff(c_317, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5' | ~r2_hidden('#skF_5', k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_297, c_154])).
% 3.05/1.54  tff(c_331, plain, (~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_44, c_42, c_38, c_155, c_317])).
% 3.05/1.54  tff(c_333, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_331])).
% 3.05/1.54  tff(c_405, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_333])).
% 3.05/1.54  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_405])).
% 3.05/1.54  tff(c_410, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_331])).
% 3.05/1.54  tff(c_414, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_410])).
% 3.05/1.54  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_414])).
% 3.05/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.54  
% 3.05/1.54  Inference rules
% 3.05/1.54  ----------------------
% 3.05/1.54  #Ref     : 0
% 3.05/1.54  #Sup     : 88
% 3.05/1.54  #Fact    : 0
% 3.05/1.54  #Define  : 0
% 3.05/1.54  #Split   : 3
% 3.05/1.54  #Chain   : 0
% 3.05/1.54  #Close   : 0
% 3.05/1.54  
% 3.05/1.54  Ordering : KBO
% 3.05/1.54  
% 3.05/1.54  Simplification rules
% 3.05/1.54  ----------------------
% 3.05/1.54  #Subsume      : 4
% 3.05/1.54  #Demod        : 34
% 3.05/1.54  #Tautology    : 36
% 3.05/1.54  #SimpNegUnit  : 0
% 3.05/1.54  #BackRed      : 0
% 3.05/1.54  
% 3.05/1.54  #Partial instantiations: 0
% 3.05/1.54  #Strategies tried      : 1
% 3.05/1.54  
% 3.05/1.54  Timing (in seconds)
% 3.05/1.54  ----------------------
% 3.05/1.54  Preprocessing        : 0.39
% 3.05/1.54  Parsing              : 0.18
% 3.05/1.54  CNF conversion       : 0.04
% 3.05/1.54  Main loop            : 0.33
% 3.05/1.54  Inferencing          : 0.13
% 3.05/1.54  Reduction            : 0.08
% 3.05/1.54  Demodulation         : 0.06
% 3.05/1.54  BG Simplification    : 0.03
% 3.05/1.54  Subsumption          : 0.07
% 3.05/1.54  Abstraction          : 0.02
% 3.05/1.54  MUC search           : 0.00
% 3.05/1.54  Cooper               : 0.00
% 3.05/1.54  Total                : 0.75
% 3.05/1.54  Index Insertion      : 0.00
% 3.05/1.54  Index Deletion       : 0.00
% 3.05/1.54  Index Matching       : 0.00
% 3.05/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
