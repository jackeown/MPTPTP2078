%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:31 EST 2020

% Result     : Theorem 4.29s
% Output     : CNFRefutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 104 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 300 expanded)
%              Number of equality atoms :    7 (  21 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_xboole_0(B,C)
           => r1_xboole_0(k10_relat_1(A,B),k10_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_funct_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

tff(c_28,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_57,plain,(
    ! [C_38,A_39,B_40] :
      ( k3_xboole_0(k10_relat_1(C_38,A_39),k10_relat_1(C_38,B_40)) = k10_relat_1(C_38,k3_xboole_0(A_39,B_40))
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1516,plain,(
    ! [C_149,A_150,B_151] :
      ( r2_hidden('#skF_1'(k10_relat_1(C_149,A_150),k10_relat_1(C_149,B_151)),k10_relat_1(C_149,k3_xboole_0(A_150,B_151)))
      | r1_xboole_0(k10_relat_1(C_149,A_150),k10_relat_1(C_149,B_151))
      | ~ v1_funct_1(C_149)
      | ~ v1_relat_1(C_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_2])).

tff(c_8,plain,(
    ! [A_6,D_17,B_13] :
      ( r2_hidden(k1_funct_1(A_6,D_17),B_13)
      | ~ r2_hidden(D_17,k10_relat_1(A_6,B_13))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_117,plain,(
    ! [A_59,B_60,C_61] :
      ( r2_hidden(k1_funct_1(A_59,'#skF_2'(A_59,B_60,C_61)),B_60)
      | r2_hidden('#skF_3'(A_59,B_60,C_61),C_61)
      | k10_relat_1(A_59,B_60) = C_61
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_163,plain,(
    ! [A_64,B_65,A_66,C_67] :
      ( ~ r1_xboole_0(A_64,B_65)
      | r2_hidden('#skF_3'(A_66,k3_xboole_0(A_64,B_65),C_67),C_67)
      | k10_relat_1(A_66,k3_xboole_0(A_64,B_65)) = C_67
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(resolution,[status(thm)],[c_117,c_4])).

tff(c_187,plain,(
    ! [B_70,B_68,A_72,A_71,A_69] :
      ( ~ r1_xboole_0(A_71,B_70)
      | ~ r1_xboole_0(A_72,B_68)
      | k3_xboole_0(A_71,B_70) = k10_relat_1(A_69,k3_xboole_0(A_72,B_68))
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(resolution,[status(thm)],[c_163,c_4])).

tff(c_191,plain,(
    ! [A_73,B_74,A_75] :
      ( ~ r1_xboole_0(A_73,B_74)
      | k10_relat_1(A_75,k3_xboole_0(A_73,B_74)) = k3_xboole_0('#skF_5','#skF_6')
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_28,c_187])).

tff(c_40,plain,(
    ! [A_31,D_32,B_33] :
      ( r2_hidden(k1_funct_1(A_31,D_32),B_33)
      | ~ r2_hidden(D_32,k10_relat_1(A_31,B_33))
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_50,plain,(
    ! [A_1,B_2,D_32,A_31] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(D_32,k10_relat_1(A_31,k3_xboole_0(A_1,B_2)))
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(resolution,[status(thm)],[c_40,c_4])).

tff(c_210,plain,(
    ! [A_73,B_74,D_32,A_75] :
      ( ~ r1_xboole_0(A_73,B_74)
      | ~ r2_hidden(D_32,k3_xboole_0('#skF_5','#skF_6'))
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75)
      | ~ r1_xboole_0(A_73,B_74)
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_50])).

tff(c_223,plain,(
    ! [A_76] :
      ( ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_225,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_223])).

tff(c_229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_225])).

tff(c_230,plain,(
    ! [A_73,B_74,D_32] :
      ( ~ r1_xboole_0(A_73,B_74)
      | ~ r1_xboole_0(A_73,B_74)
      | ~ r2_hidden(D_32,k3_xboole_0('#skF_5','#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_232,plain,(
    ! [D_77] : ~ r2_hidden(D_77,k3_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_255,plain,(
    ! [D_17,A_6] :
      ( ~ r2_hidden(D_17,k10_relat_1(A_6,k3_xboole_0('#skF_5','#skF_6')))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_232])).

tff(c_1619,plain,(
    ! [C_152] :
      ( r1_xboole_0(k10_relat_1(C_152,'#skF_5'),k10_relat_1(C_152,'#skF_6'))
      | ~ v1_funct_1(C_152)
      | ~ v1_relat_1(C_152) ) ),
    inference(resolution,[status(thm)],[c_1516,c_255])).

tff(c_26,plain,(
    ~ r1_xboole_0(k10_relat_1('#skF_4','#skF_5'),k10_relat_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1634,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1619,c_26])).

tff(c_1644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1634])).

tff(c_1646,plain,(
    ! [A_153,B_154] :
      ( ~ r1_xboole_0(A_153,B_154)
      | ~ r1_xboole_0(A_153,B_154) ) ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_1648,plain,(
    ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_1646])).

tff(c_1652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1648])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:31:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.29/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/1.79  
% 4.38/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/1.79  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.38/1.79  
% 4.38/1.79  %Foreground sorts:
% 4.38/1.79  
% 4.38/1.79  
% 4.38/1.79  %Background operators:
% 4.38/1.79  
% 4.38/1.79  
% 4.38/1.79  %Foreground operators:
% 4.38/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.38/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.38/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.38/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.38/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.38/1.79  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.38/1.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.38/1.79  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.38/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.38/1.79  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.38/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.38/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.38/1.79  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.38/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.38/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.38/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.38/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.38/1.79  
% 4.38/1.80  tff(f_69, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_xboole_0(B, C) => r1_xboole_0(k10_relat_1(A, B), k10_relat_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t141_funct_1)).
% 4.38/1.80  tff(f_59, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_funct_1)).
% 4.38/1.80  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.38/1.80  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_funct_1)).
% 4.38/1.80  tff(c_28, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.38/1.80  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.38/1.80  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.38/1.80  tff(c_57, plain, (![C_38, A_39, B_40]: (k3_xboole_0(k10_relat_1(C_38, A_39), k10_relat_1(C_38, B_40))=k10_relat_1(C_38, k3_xboole_0(A_39, B_40)) | ~v1_funct_1(C_38) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.38/1.80  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), k3_xboole_0(A_1, B_2)) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.38/1.80  tff(c_1516, plain, (![C_149, A_150, B_151]: (r2_hidden('#skF_1'(k10_relat_1(C_149, A_150), k10_relat_1(C_149, B_151)), k10_relat_1(C_149, k3_xboole_0(A_150, B_151))) | r1_xboole_0(k10_relat_1(C_149, A_150), k10_relat_1(C_149, B_151)) | ~v1_funct_1(C_149) | ~v1_relat_1(C_149))), inference(superposition, [status(thm), theory('equality')], [c_57, c_2])).
% 4.38/1.80  tff(c_8, plain, (![A_6, D_17, B_13]: (r2_hidden(k1_funct_1(A_6, D_17), B_13) | ~r2_hidden(D_17, k10_relat_1(A_6, B_13)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.38/1.80  tff(c_117, plain, (![A_59, B_60, C_61]: (r2_hidden(k1_funct_1(A_59, '#skF_2'(A_59, B_60, C_61)), B_60) | r2_hidden('#skF_3'(A_59, B_60, C_61), C_61) | k10_relat_1(A_59, B_60)=C_61 | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.38/1.80  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.38/1.80  tff(c_163, plain, (![A_64, B_65, A_66, C_67]: (~r1_xboole_0(A_64, B_65) | r2_hidden('#skF_3'(A_66, k3_xboole_0(A_64, B_65), C_67), C_67) | k10_relat_1(A_66, k3_xboole_0(A_64, B_65))=C_67 | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(resolution, [status(thm)], [c_117, c_4])).
% 4.38/1.80  tff(c_187, plain, (![B_70, B_68, A_72, A_71, A_69]: (~r1_xboole_0(A_71, B_70) | ~r1_xboole_0(A_72, B_68) | k3_xboole_0(A_71, B_70)=k10_relat_1(A_69, k3_xboole_0(A_72, B_68)) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(resolution, [status(thm)], [c_163, c_4])).
% 4.38/1.80  tff(c_191, plain, (![A_73, B_74, A_75]: (~r1_xboole_0(A_73, B_74) | k10_relat_1(A_75, k3_xboole_0(A_73, B_74))=k3_xboole_0('#skF_5', '#skF_6') | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(resolution, [status(thm)], [c_28, c_187])).
% 4.38/1.80  tff(c_40, plain, (![A_31, D_32, B_33]: (r2_hidden(k1_funct_1(A_31, D_32), B_33) | ~r2_hidden(D_32, k10_relat_1(A_31, B_33)) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.38/1.80  tff(c_50, plain, (![A_1, B_2, D_32, A_31]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(D_32, k10_relat_1(A_31, k3_xboole_0(A_1, B_2))) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(resolution, [status(thm)], [c_40, c_4])).
% 4.38/1.80  tff(c_210, plain, (![A_73, B_74, D_32, A_75]: (~r1_xboole_0(A_73, B_74) | ~r2_hidden(D_32, k3_xboole_0('#skF_5', '#skF_6')) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75) | ~r1_xboole_0(A_73, B_74) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(superposition, [status(thm), theory('equality')], [c_191, c_50])).
% 4.38/1.80  tff(c_223, plain, (![A_76]: (~v1_funct_1(A_76) | ~v1_relat_1(A_76) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(splitLeft, [status(thm)], [c_210])).
% 4.38/1.80  tff(c_225, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_223])).
% 4.38/1.80  tff(c_229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_225])).
% 4.38/1.80  tff(c_230, plain, (![A_73, B_74, D_32]: (~r1_xboole_0(A_73, B_74) | ~r1_xboole_0(A_73, B_74) | ~r2_hidden(D_32, k3_xboole_0('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_210])).
% 4.38/1.80  tff(c_232, plain, (![D_77]: (~r2_hidden(D_77, k3_xboole_0('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_230])).
% 4.38/1.80  tff(c_255, plain, (![D_17, A_6]: (~r2_hidden(D_17, k10_relat_1(A_6, k3_xboole_0('#skF_5', '#skF_6'))) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_8, c_232])).
% 4.38/1.80  tff(c_1619, plain, (![C_152]: (r1_xboole_0(k10_relat_1(C_152, '#skF_5'), k10_relat_1(C_152, '#skF_6')) | ~v1_funct_1(C_152) | ~v1_relat_1(C_152))), inference(resolution, [status(thm)], [c_1516, c_255])).
% 4.38/1.80  tff(c_26, plain, (~r1_xboole_0(k10_relat_1('#skF_4', '#skF_5'), k10_relat_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.38/1.80  tff(c_1634, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1619, c_26])).
% 4.38/1.80  tff(c_1644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1634])).
% 4.38/1.80  tff(c_1646, plain, (![A_153, B_154]: (~r1_xboole_0(A_153, B_154) | ~r1_xboole_0(A_153, B_154))), inference(splitRight, [status(thm)], [c_230])).
% 4.38/1.80  tff(c_1648, plain, (~r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_28, c_1646])).
% 4.38/1.80  tff(c_1652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1648])).
% 4.38/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/1.80  
% 4.38/1.80  Inference rules
% 4.38/1.80  ----------------------
% 4.38/1.80  #Ref     : 0
% 4.38/1.80  #Sup     : 420
% 4.38/1.80  #Fact    : 0
% 4.38/1.80  #Define  : 0
% 4.38/1.80  #Split   : 4
% 4.38/1.80  #Chain   : 0
% 4.38/1.80  #Close   : 0
% 4.38/1.80  
% 4.38/1.80  Ordering : KBO
% 4.38/1.80  
% 4.38/1.80  Simplification rules
% 4.38/1.80  ----------------------
% 4.38/1.80  #Subsume      : 171
% 4.38/1.80  #Demod        : 71
% 4.38/1.80  #Tautology    : 19
% 4.38/1.80  #SimpNegUnit  : 2
% 4.38/1.80  #BackRed      : 0
% 4.38/1.80  
% 4.38/1.80  #Partial instantiations: 0
% 4.38/1.80  #Strategies tried      : 1
% 4.38/1.80  
% 4.38/1.80  Timing (in seconds)
% 4.38/1.80  ----------------------
% 4.38/1.81  Preprocessing        : 0.31
% 4.38/1.81  Parsing              : 0.16
% 4.38/1.81  CNF conversion       : 0.02
% 4.38/1.81  Main loop            : 0.69
% 4.38/1.81  Inferencing          : 0.24
% 4.38/1.81  Reduction            : 0.15
% 4.38/1.81  Demodulation         : 0.10
% 4.38/1.81  BG Simplification    : 0.03
% 4.38/1.81  Subsumption          : 0.23
% 4.38/1.81  Abstraction          : 0.04
% 4.38/1.81  MUC search           : 0.00
% 4.38/1.81  Cooper               : 0.00
% 4.38/1.81  Total                : 1.02
% 4.38/1.81  Index Insertion      : 0.00
% 4.38/1.81  Index Deletion       : 0.00
% 4.38/1.81  Index Matching       : 0.00
% 4.38/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
