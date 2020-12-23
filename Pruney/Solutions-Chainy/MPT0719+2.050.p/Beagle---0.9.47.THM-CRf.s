%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:49 EST 2020

% Result     : Theorem 4.78s
% Output     : CNFRefutation 5.13s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 569 expanded)
%              Number of leaves         :   22 ( 209 expanded)
%              Depth                    :   14
%              Number of atoms          :  156 (1342 expanded)
%              Number of equality atoms :   27 ( 408 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_37,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_28,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_69,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_30,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_10,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_47,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_18])).

tff(c_20,plain,(
    ! [A_12] : v1_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_49,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_20])).

tff(c_4,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_159,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_1'(A_42,B_43),k1_relat_1(B_43))
      | v5_funct_1(B_43,A_42)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_167,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_1'(A_42,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_42)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_159])).

tff(c_173,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_1'(A_44,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_49,c_167])).

tff(c_24,plain,(
    ! [A_13,B_14] : k1_relat_1('#skF_2'(A_13,B_14)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    ! [A_13,B_14] : v1_relat_1('#skF_2'(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_85,plain,(
    ! [A_29] :
      ( k1_relat_1(A_29) != k1_xboole_0
      | k1_xboole_0 = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_88,plain,(
    ! [A_13,B_14] :
      ( k1_relat_1('#skF_2'(A_13,B_14)) != k1_xboole_0
      | '#skF_2'(A_13,B_14) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_85])).

tff(c_117,plain,(
    ! [A_33,B_34] :
      ( k1_xboole_0 != A_33
      | '#skF_2'(A_33,B_34) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_88])).

tff(c_22,plain,(
    ! [A_13,B_14,D_19] :
      ( k1_funct_1('#skF_2'(A_13,B_14),D_19) = B_14
      | ~ r2_hidden(D_19,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_123,plain,(
    ! [D_19,B_34,A_33] :
      ( k1_funct_1(k1_xboole_0,D_19) = B_34
      | ~ r2_hidden(D_19,A_33)
      | k1_xboole_0 != A_33 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_22])).

tff(c_187,plain,(
    ! [A_45] :
      ( k1_funct_1(k1_xboole_0,'#skF_1'(A_45,k1_xboole_0)) = '#skF_3'
      | v5_funct_1(k1_xboole_0,A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_173,c_123])).

tff(c_176,plain,(
    ! [A_44,B_34] :
      ( k1_funct_1(k1_xboole_0,'#skF_1'(A_44,k1_xboole_0)) = B_34
      | v5_funct_1(k1_xboole_0,A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_173,c_123])).

tff(c_190,plain,(
    ! [B_34,A_45] :
      ( B_34 = '#skF_3'
      | v5_funct_1(k1_xboole_0,A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45)
      | v5_funct_1(k1_xboole_0,A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_176])).

tff(c_3899,plain,(
    ! [A_45] :
      ( v5_funct_1(k1_xboole_0,A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45)
      | v5_funct_1(k1_xboole_0,A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_3913,plain,(
    ! [A_3010] :
      ( ~ v1_funct_1(A_3010)
      | ~ v1_relat_1(A_3010)
      | v5_funct_1(k1_xboole_0,A_3010) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3899])).

tff(c_3916,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3913,c_30])).

tff(c_3920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3916])).

tff(c_3942,plain,(
    ! [B_3042] : B_3042 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_207,plain,(
    ! [A_45] :
      ( k1_funct_1(k1_xboole_0,'#skF_1'(A_45,k1_xboole_0)) = k1_xboole_0
      | v5_funct_1(k1_xboole_0,A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_173,c_123])).

tff(c_210,plain,(
    ! [B_34,A_45] :
      ( k1_xboole_0 = B_34
      | v5_funct_1(k1_xboole_0,A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45)
      | v5_funct_1(k1_xboole_0,A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_176])).

tff(c_2659,plain,(
    ! [A_45] :
      ( v5_funct_1(k1_xboole_0,A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45)
      | v5_funct_1(k1_xboole_0,A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_2700,plain,(
    ! [A_1990] :
      ( ~ v1_funct_1(A_1990)
      | ~ v1_relat_1(A_1990)
      | v5_funct_1(k1_xboole_0,A_1990) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2659])).

tff(c_2706,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2700,c_30])).

tff(c_2713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2706])).

tff(c_2838,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_902,plain,(
    ! [B_655,A_656] :
      ( ~ r2_hidden(k1_funct_1(B_655,'#skF_1'(A_656,B_655)),k1_funct_1(A_656,'#skF_1'(A_656,B_655)))
      | v5_funct_1(B_655,A_656)
      | ~ v1_funct_1(B_655)
      | ~ v1_relat_1(B_655)
      | ~ v1_funct_1(A_656)
      | ~ v1_relat_1(A_656) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_929,plain,(
    ! [B_34] :
      ( ~ r2_hidden(k1_funct_1(k1_xboole_0,'#skF_1'(k1_xboole_0,k1_xboole_0)),B_34)
      | v5_funct_1(k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | v5_funct_1(k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_902])).

tff(c_942,plain,(
    ! [B_34] :
      ( ~ r2_hidden(k1_funct_1(k1_xboole_0,'#skF_1'(k1_xboole_0,k1_xboole_0)),B_34)
      | v5_funct_1(k1_xboole_0,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_49,c_47,c_49,c_47,c_49,c_929])).

tff(c_948,plain,(
    ! [B_675] : ~ r2_hidden(k1_funct_1(k1_xboole_0,'#skF_1'(k1_xboole_0,k1_xboole_0)),B_675) ),
    inference(splitLeft,[status(thm)],[c_942])).

tff(c_957,plain,(
    ! [B_34,B_675] :
      ( ~ r2_hidden(B_34,B_675)
      | v5_funct_1(k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_948])).

tff(c_962,plain,(
    ! [B_34,B_675] :
      ( ~ r2_hidden(B_34,B_675)
      | v5_funct_1(k1_xboole_0,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_49,c_957])).

tff(c_963,plain,(
    ! [B_34,B_675] : ~ r2_hidden(B_34,B_675) ),
    inference(splitLeft,[status(thm)],[c_962])).

tff(c_172,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_1'(A_42,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_42)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_49,c_167])).

tff(c_1075,plain,(
    ! [A_733] :
      ( v5_funct_1(k1_xboole_0,A_733)
      | ~ v1_funct_1(A_733)
      | ~ v1_relat_1(A_733) ) ),
    inference(negUnitSimplification,[status(thm)],[c_963,c_172])).

tff(c_1078,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1075,c_30])).

tff(c_1082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1078])).

tff(c_1083,plain,(
    v5_funct_1(k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_962])).

tff(c_2839,plain,(
    v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2838,c_1083])).

tff(c_2968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2839])).

tff(c_2969,plain,(
    v5_funct_1(k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_942])).

tff(c_4010,plain,(
    v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3942,c_2969])).

tff(c_4136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_4010])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.78/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.91  
% 4.78/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.91  %$ v5_funct_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 4.78/1.91  
% 4.78/1.91  %Foreground sorts:
% 4.78/1.91  
% 4.78/1.91  
% 4.78/1.91  %Background operators:
% 4.78/1.91  
% 4.78/1.91  
% 4.78/1.91  %Foreground operators:
% 4.78/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.78/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.78/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.78/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.78/1.91  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 4.78/1.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.78/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.78/1.91  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.78/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.78/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.78/1.91  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.78/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.78/1.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.78/1.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.78/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.78/1.91  
% 5.13/1.93  tff(f_76, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 5.13/1.93  tff(f_37, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 5.13/1.93  tff(f_57, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.13/1.93  tff(f_28, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.13/1.93  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 5.13/1.93  tff(f_69, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 5.13/1.93  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.13/1.93  tff(c_30, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.13/1.93  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.13/1.93  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.13/1.93  tff(c_10, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.13/1.93  tff(c_18, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.13/1.93  tff(c_47, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_18])).
% 5.13/1.93  tff(c_20, plain, (![A_12]: (v1_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.13/1.93  tff(c_49, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_20])).
% 5.13/1.93  tff(c_4, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.13/1.93  tff(c_159, plain, (![A_42, B_43]: (r2_hidden('#skF_1'(A_42, B_43), k1_relat_1(B_43)) | v5_funct_1(B_43, A_42) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.13/1.93  tff(c_167, plain, (![A_42]: (r2_hidden('#skF_1'(A_42, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_42) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(superposition, [status(thm), theory('equality')], [c_4, c_159])).
% 5.13/1.93  tff(c_173, plain, (![A_44]: (r2_hidden('#skF_1'(A_44, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_49, c_167])).
% 5.13/1.93  tff(c_24, plain, (![A_13, B_14]: (k1_relat_1('#skF_2'(A_13, B_14))=A_13)), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.13/1.93  tff(c_28, plain, (![A_13, B_14]: (v1_relat_1('#skF_2'(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.13/1.93  tff(c_85, plain, (![A_29]: (k1_relat_1(A_29)!=k1_xboole_0 | k1_xboole_0=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.13/1.93  tff(c_88, plain, (![A_13, B_14]: (k1_relat_1('#skF_2'(A_13, B_14))!=k1_xboole_0 | '#skF_2'(A_13, B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_85])).
% 5.13/1.93  tff(c_117, plain, (![A_33, B_34]: (k1_xboole_0!=A_33 | '#skF_2'(A_33, B_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_88])).
% 5.13/1.93  tff(c_22, plain, (![A_13, B_14, D_19]: (k1_funct_1('#skF_2'(A_13, B_14), D_19)=B_14 | ~r2_hidden(D_19, A_13))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.13/1.93  tff(c_123, plain, (![D_19, B_34, A_33]: (k1_funct_1(k1_xboole_0, D_19)=B_34 | ~r2_hidden(D_19, A_33) | k1_xboole_0!=A_33)), inference(superposition, [status(thm), theory('equality')], [c_117, c_22])).
% 5.13/1.93  tff(c_187, plain, (![A_45]: (k1_funct_1(k1_xboole_0, '#skF_1'(A_45, k1_xboole_0))='#skF_3' | v5_funct_1(k1_xboole_0, A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_173, c_123])).
% 5.13/1.93  tff(c_176, plain, (![A_44, B_34]: (k1_funct_1(k1_xboole_0, '#skF_1'(A_44, k1_xboole_0))=B_34 | v5_funct_1(k1_xboole_0, A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(resolution, [status(thm)], [c_173, c_123])).
% 5.13/1.93  tff(c_190, plain, (![B_34, A_45]: (B_34='#skF_3' | v5_funct_1(k1_xboole_0, A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45) | v5_funct_1(k1_xboole_0, A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_187, c_176])).
% 5.13/1.93  tff(c_3899, plain, (![A_45]: (v5_funct_1(k1_xboole_0, A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45) | v5_funct_1(k1_xboole_0, A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(splitLeft, [status(thm)], [c_190])).
% 5.13/1.93  tff(c_3913, plain, (![A_3010]: (~v1_funct_1(A_3010) | ~v1_relat_1(A_3010) | v5_funct_1(k1_xboole_0, A_3010))), inference(factorization, [status(thm), theory('equality')], [c_3899])).
% 5.13/1.93  tff(c_3916, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3913, c_30])).
% 5.13/1.93  tff(c_3920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3916])).
% 5.13/1.93  tff(c_3942, plain, (![B_3042]: (B_3042='#skF_3')), inference(splitRight, [status(thm)], [c_190])).
% 5.13/1.93  tff(c_207, plain, (![A_45]: (k1_funct_1(k1_xboole_0, '#skF_1'(A_45, k1_xboole_0))=k1_xboole_0 | v5_funct_1(k1_xboole_0, A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_173, c_123])).
% 5.13/1.93  tff(c_210, plain, (![B_34, A_45]: (k1_xboole_0=B_34 | v5_funct_1(k1_xboole_0, A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45) | v5_funct_1(k1_xboole_0, A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_207, c_176])).
% 5.13/1.93  tff(c_2659, plain, (![A_45]: (v5_funct_1(k1_xboole_0, A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45) | v5_funct_1(k1_xboole_0, A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(splitLeft, [status(thm)], [c_210])).
% 5.13/1.93  tff(c_2700, plain, (![A_1990]: (~v1_funct_1(A_1990) | ~v1_relat_1(A_1990) | v5_funct_1(k1_xboole_0, A_1990))), inference(factorization, [status(thm), theory('equality')], [c_2659])).
% 5.13/1.93  tff(c_2706, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2700, c_30])).
% 5.13/1.93  tff(c_2713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_2706])).
% 5.13/1.93  tff(c_2838, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_210])).
% 5.13/1.93  tff(c_902, plain, (![B_655, A_656]: (~r2_hidden(k1_funct_1(B_655, '#skF_1'(A_656, B_655)), k1_funct_1(A_656, '#skF_1'(A_656, B_655))) | v5_funct_1(B_655, A_656) | ~v1_funct_1(B_655) | ~v1_relat_1(B_655) | ~v1_funct_1(A_656) | ~v1_relat_1(A_656))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.13/1.93  tff(c_929, plain, (![B_34]: (~r2_hidden(k1_funct_1(k1_xboole_0, '#skF_1'(k1_xboole_0, k1_xboole_0)), B_34) | v5_funct_1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | v5_funct_1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_176, c_902])).
% 5.13/1.93  tff(c_942, plain, (![B_34]: (~r2_hidden(k1_funct_1(k1_xboole_0, '#skF_1'(k1_xboole_0, k1_xboole_0)), B_34) | v5_funct_1(k1_xboole_0, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_49, c_47, c_49, c_47, c_49, c_929])).
% 5.13/1.93  tff(c_948, plain, (![B_675]: (~r2_hidden(k1_funct_1(k1_xboole_0, '#skF_1'(k1_xboole_0, k1_xboole_0)), B_675))), inference(splitLeft, [status(thm)], [c_942])).
% 5.13/1.93  tff(c_957, plain, (![B_34, B_675]: (~r2_hidden(B_34, B_675) | v5_funct_1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_176, c_948])).
% 5.13/1.93  tff(c_962, plain, (![B_34, B_675]: (~r2_hidden(B_34, B_675) | v5_funct_1(k1_xboole_0, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_49, c_957])).
% 5.13/1.93  tff(c_963, plain, (![B_34, B_675]: (~r2_hidden(B_34, B_675))), inference(splitLeft, [status(thm)], [c_962])).
% 5.13/1.93  tff(c_172, plain, (![A_42]: (r2_hidden('#skF_1'(A_42, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_42) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_49, c_167])).
% 5.13/1.93  tff(c_1075, plain, (![A_733]: (v5_funct_1(k1_xboole_0, A_733) | ~v1_funct_1(A_733) | ~v1_relat_1(A_733))), inference(negUnitSimplification, [status(thm)], [c_963, c_172])).
% 5.13/1.93  tff(c_1078, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1075, c_30])).
% 5.13/1.93  tff(c_1082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1078])).
% 5.13/1.93  tff(c_1083, plain, (v5_funct_1(k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_962])).
% 5.13/1.93  tff(c_2839, plain, (v5_funct_1(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2838, c_1083])).
% 5.13/1.93  tff(c_2968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_2839])).
% 5.13/1.93  tff(c_2969, plain, (v5_funct_1(k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_942])).
% 5.13/1.93  tff(c_4010, plain, (v5_funct_1(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3942, c_2969])).
% 5.13/1.93  tff(c_4136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_4010])).
% 5.13/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/1.93  
% 5.13/1.93  Inference rules
% 5.13/1.93  ----------------------
% 5.13/1.93  #Ref     : 0
% 5.13/1.93  #Sup     : 1067
% 5.13/1.93  #Fact    : 4
% 5.13/1.93  #Define  : 0
% 5.13/1.93  #Split   : 8
% 5.13/1.93  #Chain   : 0
% 5.13/1.93  #Close   : 0
% 5.13/1.93  
% 5.13/1.93  Ordering : KBO
% 5.13/1.93  
% 5.13/1.93  Simplification rules
% 5.13/1.93  ----------------------
% 5.13/1.93  #Subsume      : 171
% 5.13/1.93  #Demod        : 225
% 5.13/1.93  #Tautology    : 82
% 5.13/1.93  #SimpNegUnit  : 5
% 5.13/1.93  #BackRed      : 2
% 5.13/1.93  
% 5.13/1.93  #Partial instantiations: 2313
% 5.13/1.93  #Strategies tried      : 1
% 5.13/1.93  
% 5.13/1.93  Timing (in seconds)
% 5.13/1.93  ----------------------
% 5.13/1.93  Preprocessing        : 0.28
% 5.13/1.93  Parsing              : 0.16
% 5.13/1.93  CNF conversion       : 0.02
% 5.13/1.93  Main loop            : 0.89
% 5.13/1.93  Inferencing          : 0.34
% 5.13/1.93  Reduction            : 0.27
% 5.13/1.93  Demodulation         : 0.20
% 5.13/1.93  BG Simplification    : 0.04
% 5.13/1.93  Subsumption          : 0.18
% 5.13/1.93  Abstraction          : 0.04
% 5.13/1.93  MUC search           : 0.00
% 5.13/1.93  Cooper               : 0.00
% 5.13/1.93  Total                : 1.20
% 5.13/1.93  Index Insertion      : 0.00
% 5.13/1.93  Index Deletion       : 0.00
% 5.13/1.93  Index Matching       : 0.00
% 5.13/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
