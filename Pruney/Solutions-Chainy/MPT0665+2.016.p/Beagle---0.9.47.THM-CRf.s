%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:16 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :   48 (  93 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 246 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( v1_funct_1(k7_relat_1(A_11,B_12))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( k3_xboole_0(k1_relat_1(B_10),A_9) = k1_relat_1(k7_relat_1(B_10,A_9))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,(
    ! [D_30,A_31,B_32] :
      ( r2_hidden(D_30,k3_xboole_0(A_31,B_32))
      | ~ r2_hidden(D_30,B_32)
      | ~ r2_hidden(D_30,A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_69,plain,(
    ! [D_30,B_10,A_9] :
      ( r2_hidden(D_30,k1_relat_1(k7_relat_1(B_10,A_9)))
      | ~ r2_hidden(D_30,A_9)
      | ~ r2_hidden(D_30,k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_60])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [C_41,B_42,A_43] :
      ( k1_funct_1(k7_relat_1(C_41,B_42),A_43) = k1_funct_1(C_41,A_43)
      | ~ r2_hidden(A_43,B_42)
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    ! [B_14,A_13] :
      ( r2_hidden(k1_funct_1(B_14,A_13),k2_relat_1(B_14))
      | ~ r2_hidden(A_13,k1_relat_1(B_14))
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1830,plain,(
    ! [C_171,A_172,B_173] :
      ( r2_hidden(k1_funct_1(C_171,A_172),k2_relat_1(k7_relat_1(C_171,B_173)))
      | ~ r2_hidden(A_172,k1_relat_1(k7_relat_1(C_171,B_173)))
      | ~ v1_funct_1(k7_relat_1(C_171,B_173))
      | ~ v1_relat_1(k7_relat_1(C_171,B_173))
      | ~ r2_hidden(A_172,B_173)
      | ~ v1_funct_1(C_171)
      | ~ v1_relat_1(C_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_28])).

tff(c_32,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),k2_relat_1(k7_relat_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1833,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1(k7_relat_1('#skF_5','#skF_4')))
    | ~ v1_funct_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1830,c_32])).

tff(c_1839,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1(k7_relat_1('#skF_5','#skF_4')))
    | ~ v1_funct_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_1833])).

tff(c_1840,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1839])).

tff(c_1843,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_1840])).

tff(c_1847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1843])).

tff(c_1848,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_relat_1(k7_relat_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1839])).

tff(c_1850,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1(k7_relat_1('#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1848])).

tff(c_1853,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_69,c_1850])).

tff(c_1857,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_34,c_1853])).

tff(c_1858,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1848])).

tff(c_1862,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1858])).

tff(c_1866,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1862])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.07/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.70  
% 4.07/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.71  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 4.07/1.71  
% 4.07/1.71  %Foreground sorts:
% 4.07/1.71  
% 4.07/1.71  
% 4.07/1.71  %Background operators:
% 4.07/1.71  
% 4.07/1.71  
% 4.07/1.71  %Foreground operators:
% 4.07/1.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.07/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.07/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.07/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.07/1.71  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.07/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.07/1.71  tff('#skF_5', type, '#skF_5': $i).
% 4.07/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.07/1.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.07/1.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.07/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.07/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.07/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.07/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.07/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.07/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.07/1.71  
% 4.07/1.72  tff(f_77, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_1)).
% 4.07/1.72  tff(f_50, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 4.07/1.72  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 4.07/1.72  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.07/1.72  tff(f_38, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.07/1.72  tff(f_66, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 4.07/1.72  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 4.07/1.72  tff(c_40, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.07/1.72  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.07/1.72  tff(c_24, plain, (![A_11, B_12]: (v1_funct_1(k7_relat_1(A_11, B_12)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.07/1.72  tff(c_36, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.07/1.72  tff(c_34, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.07/1.72  tff(c_22, plain, (![B_10, A_9]: (k3_xboole_0(k1_relat_1(B_10), A_9)=k1_relat_1(k7_relat_1(B_10, A_9)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.07/1.72  tff(c_60, plain, (![D_30, A_31, B_32]: (r2_hidden(D_30, k3_xboole_0(A_31, B_32)) | ~r2_hidden(D_30, B_32) | ~r2_hidden(D_30, A_31))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.07/1.72  tff(c_69, plain, (![D_30, B_10, A_9]: (r2_hidden(D_30, k1_relat_1(k7_relat_1(B_10, A_9))) | ~r2_hidden(D_30, A_9) | ~r2_hidden(D_30, k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(superposition, [status(thm), theory('equality')], [c_22, c_60])).
% 4.07/1.72  tff(c_20, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.07/1.72  tff(c_75, plain, (![C_41, B_42, A_43]: (k1_funct_1(k7_relat_1(C_41, B_42), A_43)=k1_funct_1(C_41, A_43) | ~r2_hidden(A_43, B_42) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.07/1.72  tff(c_28, plain, (![B_14, A_13]: (r2_hidden(k1_funct_1(B_14, A_13), k2_relat_1(B_14)) | ~r2_hidden(A_13, k1_relat_1(B_14)) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.07/1.72  tff(c_1830, plain, (![C_171, A_172, B_173]: (r2_hidden(k1_funct_1(C_171, A_172), k2_relat_1(k7_relat_1(C_171, B_173))) | ~r2_hidden(A_172, k1_relat_1(k7_relat_1(C_171, B_173))) | ~v1_funct_1(k7_relat_1(C_171, B_173)) | ~v1_relat_1(k7_relat_1(C_171, B_173)) | ~r2_hidden(A_172, B_173) | ~v1_funct_1(C_171) | ~v1_relat_1(C_171))), inference(superposition, [status(thm), theory('equality')], [c_75, c_28])).
% 4.07/1.72  tff(c_32, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), k2_relat_1(k7_relat_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.07/1.72  tff(c_1833, plain, (~r2_hidden('#skF_3', k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))) | ~v1_funct_1(k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1830, c_32])).
% 4.07/1.72  tff(c_1839, plain, (~r2_hidden('#skF_3', k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))) | ~v1_funct_1(k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_1833])).
% 4.07/1.72  tff(c_1840, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1839])).
% 4.07/1.72  tff(c_1843, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_1840])).
% 4.07/1.72  tff(c_1847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1843])).
% 4.07/1.72  tff(c_1848, plain, (~v1_funct_1(k7_relat_1('#skF_5', '#skF_4')) | ~r2_hidden('#skF_3', k1_relat_1(k7_relat_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_1839])).
% 4.07/1.72  tff(c_1850, plain, (~r2_hidden('#skF_3', k1_relat_1(k7_relat_1('#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_1848])).
% 4.07/1.72  tff(c_1853, plain, (~r2_hidden('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_69, c_1850])).
% 4.07/1.72  tff(c_1857, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_34, c_1853])).
% 4.07/1.72  tff(c_1858, plain, (~v1_funct_1(k7_relat_1('#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_1848])).
% 4.07/1.72  tff(c_1862, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_1858])).
% 4.07/1.72  tff(c_1866, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1862])).
% 4.07/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.72  
% 4.07/1.72  Inference rules
% 4.07/1.72  ----------------------
% 4.07/1.72  #Ref     : 0
% 4.07/1.72  #Sup     : 411
% 4.07/1.72  #Fact    : 0
% 4.07/1.72  #Define  : 0
% 4.07/1.72  #Split   : 2
% 4.07/1.72  #Chain   : 0
% 4.07/1.72  #Close   : 0
% 4.07/1.72  
% 4.07/1.72  Ordering : KBO
% 4.07/1.72  
% 4.07/1.72  Simplification rules
% 4.07/1.72  ----------------------
% 4.07/1.72  #Subsume      : 95
% 4.07/1.72  #Demod        : 107
% 4.07/1.72  #Tautology    : 27
% 4.07/1.72  #SimpNegUnit  : 0
% 4.07/1.72  #BackRed      : 0
% 4.07/1.72  
% 4.07/1.72  #Partial instantiations: 0
% 4.07/1.72  #Strategies tried      : 1
% 4.07/1.72  
% 4.07/1.72  Timing (in seconds)
% 4.07/1.72  ----------------------
% 4.07/1.72  Preprocessing        : 0.31
% 4.07/1.72  Parsing              : 0.16
% 4.07/1.72  CNF conversion       : 0.02
% 4.07/1.72  Main loop            : 0.66
% 4.07/1.72  Inferencing          : 0.25
% 4.07/1.72  Reduction            : 0.15
% 4.07/1.72  Demodulation         : 0.11
% 4.07/1.72  BG Simplification    : 0.03
% 4.07/1.72  Subsumption          : 0.17
% 4.07/1.72  Abstraction          : 0.04
% 4.07/1.72  MUC search           : 0.00
% 4.07/1.72  Cooper               : 0.00
% 4.07/1.72  Total                : 0.99
% 4.07/1.72  Index Insertion      : 0.00
% 4.07/1.72  Index Deletion       : 0.00
% 4.07/1.72  Index Matching       : 0.00
% 4.07/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
