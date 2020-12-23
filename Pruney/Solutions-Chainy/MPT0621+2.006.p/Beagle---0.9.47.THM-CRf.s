%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:59 EST 2020

% Result     : Theorem 9.71s
% Output     : CNFRefutation 9.71s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 236 expanded)
%              Number of leaves         :   29 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  137 ( 707 expanded)
%              Number of equality atoms :   76 ( 353 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > np__1 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(np__1,type,(
    np__1: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_43,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_76,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_78,axiom,(
    ~ v1_xboole_0(np__1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',spc1_boole)).

tff(c_26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    ! [A_16] : k3_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_712,plain,(
    ! [A_98,B_99] :
      ( r2_hidden('#skF_4'(A_98,B_99),B_99)
      | r2_hidden('#skF_5'(A_98,B_99),A_98)
      | B_99 = A_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [D_12,A_7,B_8] :
      ( r2_hidden(D_12,A_7)
      | ~ r2_hidden(D_12,k3_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5975,plain,(
    ! [A_301,B_302,B_303] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_301,B_302),B_303),A_301)
      | r2_hidden('#skF_4'(k3_xboole_0(A_301,B_302),B_303),B_303)
      | k3_xboole_0(A_301,B_302) = B_303 ) ),
    inference(resolution,[status(thm)],[c_712,c_12])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_4'(A_13,B_14),B_14)
      | ~ r2_hidden('#skF_5'(A_13,B_14),B_14)
      | B_14 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10902,plain,(
    ! [A_359,B_360] :
      ( r2_hidden('#skF_4'(k3_xboole_0(A_359,B_360),A_359),A_359)
      | k3_xboole_0(A_359,B_360) = A_359 ) ),
    inference(resolution,[status(thm)],[c_5975,c_30])).

tff(c_11014,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_4'(k1_xboole_0,A_16),A_16)
      | k3_xboole_0(A_16,k1_xboole_0) = A_16 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_10902])).

tff(c_11033,plain,(
    ! [A_361] :
      ( r2_hidden('#skF_4'(k1_xboole_0,A_361),A_361)
      | k1_xboole_0 = A_361 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_11014])).

tff(c_42,plain,(
    ! [A_17] : v1_funct_1('#skF_6'(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_40,plain,(
    ! [A_17] : k1_relat_1('#skF_6'(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44,plain,(
    ! [A_17] : v1_relat_1('#skF_6'(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_50,plain,(
    ! [A_23] : v1_funct_1('#skF_7'(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_48,plain,(
    ! [A_23] : k1_relat_1('#skF_7'(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_52,plain,(
    ! [A_23] : v1_relat_1('#skF_7'(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_79,plain,(
    ! [C_41,B_42] :
      ( C_41 = B_42
      | k1_relat_1(C_41) != '#skF_8'
      | k1_relat_1(B_42) != '#skF_8'
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_83,plain,(
    ! [B_42,A_23] :
      ( B_42 = '#skF_7'(A_23)
      | k1_relat_1('#skF_7'(A_23)) != '#skF_8'
      | k1_relat_1(B_42) != '#skF_8'
      | ~ v1_funct_1('#skF_7'(A_23))
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(resolution,[status(thm)],[c_52,c_79])).

tff(c_207,plain,(
    ! [B_53,A_54] :
      ( B_53 = '#skF_7'(A_54)
      | A_54 != '#skF_8'
      | k1_relat_1(B_53) != '#skF_8'
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_83])).

tff(c_209,plain,(
    ! [A_54,A_17] :
      ( '#skF_7'(A_54) = '#skF_6'(A_17)
      | A_54 != '#skF_8'
      | k1_relat_1('#skF_6'(A_17)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_17)) ) ),
    inference(resolution,[status(thm)],[c_44,c_207])).

tff(c_286,plain,(
    ! [A_67,A_68] :
      ( '#skF_7'(A_67) = '#skF_6'(A_68)
      | A_67 != '#skF_8'
      | A_68 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_209])).

tff(c_38,plain,(
    ! [A_17,C_22] :
      ( k1_funct_1('#skF_6'(A_17),C_22) = k1_xboole_0
      | ~ r2_hidden(C_22,A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_295,plain,(
    ! [A_67,C_22,A_68] :
      ( k1_funct_1('#skF_7'(A_67),C_22) = k1_xboole_0
      | ~ r2_hidden(C_22,A_68)
      | A_67 != '#skF_8'
      | A_68 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_38])).

tff(c_12992,plain,(
    ! [A_393,A_394] :
      ( k1_funct_1('#skF_7'(A_393),'#skF_4'(k1_xboole_0,A_394)) = k1_xboole_0
      | A_393 != '#skF_8'
      | A_394 != '#skF_8'
      | k1_xboole_0 = A_394 ) ),
    inference(resolution,[status(thm)],[c_11033,c_295])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1399,plain,(
    ! [A_138,B_139] :
      ( ~ v1_xboole_0(A_138)
      | r2_hidden('#skF_4'(A_138,B_139),B_139)
      | B_139 = A_138 ) ),
    inference(resolution,[status(thm)],[c_712,c_4])).

tff(c_211,plain,(
    ! [A_54,A_23] :
      ( '#skF_7'(A_54) = '#skF_7'(A_23)
      | A_54 != '#skF_8'
      | k1_relat_1('#skF_7'(A_23)) != '#skF_8'
      | ~ v1_funct_1('#skF_7'(A_23)) ) ),
    inference(resolution,[status(thm)],[c_52,c_207])).

tff(c_344,plain,(
    ! [A_74,A_73] :
      ( '#skF_7'(A_74) = '#skF_7'(A_73)
      | A_73 != '#skF_8'
      | A_74 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_211])).

tff(c_46,plain,(
    ! [A_23,C_28] :
      ( k1_funct_1('#skF_7'(A_23),C_28) = np__1
      | ~ r2_hidden(C_28,A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_368,plain,(
    ! [A_73,C_28,A_74] :
      ( k1_funct_1('#skF_7'(A_73),C_28) = np__1
      | ~ r2_hidden(C_28,A_74)
      | A_73 != '#skF_8'
      | A_74 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_46])).

tff(c_1422,plain,(
    ! [A_73,A_138,B_139] :
      ( k1_funct_1('#skF_7'(A_73),'#skF_4'(A_138,B_139)) = np__1
      | A_73 != '#skF_8'
      | B_139 != '#skF_8'
      | ~ v1_xboole_0(A_138)
      | B_139 = A_138 ) ),
    inference(resolution,[status(thm)],[c_1399,c_368])).

tff(c_12998,plain,(
    ! [A_393,A_394] :
      ( np__1 = k1_xboole_0
      | A_393 != '#skF_8'
      | A_394 != '#skF_8'
      | ~ v1_xboole_0(k1_xboole_0)
      | k1_xboole_0 = A_394
      | A_393 != '#skF_8'
      | A_394 != '#skF_8'
      | k1_xboole_0 = A_394 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12992,c_1422])).

tff(c_13024,plain,(
    ! [A_393,A_394] :
      ( np__1 = k1_xboole_0
      | A_393 != '#skF_8'
      | A_394 != '#skF_8'
      | k1_xboole_0 = A_394 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12998])).

tff(c_13028,plain,(
    ! [A_393] : A_393 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_13024])).

tff(c_13032,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_13028])).

tff(c_13033,plain,(
    ! [A_394] :
      ( np__1 = k1_xboole_0
      | A_394 != '#skF_8'
      | k1_xboole_0 = A_394 ) ),
    inference(splitRight,[status(thm)],[c_13024])).

tff(c_13034,plain,(
    np__1 = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_13033])).

tff(c_54,plain,(
    ~ v1_xboole_0(np__1) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_13044,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13034,c_54])).

tff(c_13047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_13044])).

tff(c_13320,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_13033])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_13358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13320,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:53:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.71/3.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.71/3.45  
% 9.71/3.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.71/3.45  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > np__1 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_6 > #skF_4
% 9.71/3.45  
% 9.71/3.45  %Foreground sorts:
% 9.71/3.45  
% 9.71/3.45  
% 9.71/3.45  %Background operators:
% 9.71/3.45  
% 9.71/3.45  
% 9.71/3.45  %Foreground operators:
% 9.71/3.45  tff('#skF_7', type, '#skF_7': $i > $i).
% 9.71/3.45  tff(np__1, type, np__1: $i).
% 9.71/3.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.71/3.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.71/3.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.71/3.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.71/3.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.71/3.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.71/3.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.71/3.45  tff('#skF_8', type, '#skF_8': $i).
% 9.71/3.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.71/3.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.71/3.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.71/3.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.71/3.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.71/3.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.71/3.45  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.71/3.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.71/3.45  tff('#skF_6', type, '#skF_6': $i > $i).
% 9.71/3.45  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.71/3.45  
% 9.71/3.46  tff(f_43, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.71/3.46  tff(f_52, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 9.71/3.46  tff(f_50, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 9.71/3.46  tff(f_42, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 9.71/3.46  tff(f_64, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 9.71/3.46  tff(f_76, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 9.71/3.46  tff(f_97, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 9.71/3.46  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.71/3.46  tff(f_78, axiom, ~v1_xboole_0(np__1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', spc1_boole)).
% 9.71/3.46  tff(c_26, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.71/3.46  tff(c_36, plain, (![A_16]: (k3_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.71/3.46  tff(c_712, plain, (![A_98, B_99]: (r2_hidden('#skF_4'(A_98, B_99), B_99) | r2_hidden('#skF_5'(A_98, B_99), A_98) | B_99=A_98)), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.71/3.46  tff(c_12, plain, (![D_12, A_7, B_8]: (r2_hidden(D_12, A_7) | ~r2_hidden(D_12, k3_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.71/3.46  tff(c_5975, plain, (![A_301, B_302, B_303]: (r2_hidden('#skF_5'(k3_xboole_0(A_301, B_302), B_303), A_301) | r2_hidden('#skF_4'(k3_xboole_0(A_301, B_302), B_303), B_303) | k3_xboole_0(A_301, B_302)=B_303)), inference(resolution, [status(thm)], [c_712, c_12])).
% 9.71/3.46  tff(c_30, plain, (![A_13, B_14]: (r2_hidden('#skF_4'(A_13, B_14), B_14) | ~r2_hidden('#skF_5'(A_13, B_14), B_14) | B_14=A_13)), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.71/3.46  tff(c_10902, plain, (![A_359, B_360]: (r2_hidden('#skF_4'(k3_xboole_0(A_359, B_360), A_359), A_359) | k3_xboole_0(A_359, B_360)=A_359)), inference(resolution, [status(thm)], [c_5975, c_30])).
% 9.71/3.46  tff(c_11014, plain, (![A_16]: (r2_hidden('#skF_4'(k1_xboole_0, A_16), A_16) | k3_xboole_0(A_16, k1_xboole_0)=A_16)), inference(superposition, [status(thm), theory('equality')], [c_36, c_10902])).
% 9.71/3.46  tff(c_11033, plain, (![A_361]: (r2_hidden('#skF_4'(k1_xboole_0, A_361), A_361) | k1_xboole_0=A_361)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_11014])).
% 9.71/3.46  tff(c_42, plain, (![A_17]: (v1_funct_1('#skF_6'(A_17)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.71/3.46  tff(c_40, plain, (![A_17]: (k1_relat_1('#skF_6'(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.71/3.46  tff(c_44, plain, (![A_17]: (v1_relat_1('#skF_6'(A_17)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.71/3.46  tff(c_50, plain, (![A_23]: (v1_funct_1('#skF_7'(A_23)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.71/3.46  tff(c_48, plain, (![A_23]: (k1_relat_1('#skF_7'(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.71/3.46  tff(c_52, plain, (![A_23]: (v1_relat_1('#skF_7'(A_23)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.71/3.46  tff(c_79, plain, (![C_41, B_42]: (C_41=B_42 | k1_relat_1(C_41)!='#skF_8' | k1_relat_1(B_42)!='#skF_8' | ~v1_funct_1(C_41) | ~v1_relat_1(C_41) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.71/3.46  tff(c_83, plain, (![B_42, A_23]: (B_42='#skF_7'(A_23) | k1_relat_1('#skF_7'(A_23))!='#skF_8' | k1_relat_1(B_42)!='#skF_8' | ~v1_funct_1('#skF_7'(A_23)) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_52, c_79])).
% 9.71/3.46  tff(c_207, plain, (![B_53, A_54]: (B_53='#skF_7'(A_54) | A_54!='#skF_8' | k1_relat_1(B_53)!='#skF_8' | ~v1_funct_1(B_53) | ~v1_relat_1(B_53))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_83])).
% 9.71/3.46  tff(c_209, plain, (![A_54, A_17]: ('#skF_7'(A_54)='#skF_6'(A_17) | A_54!='#skF_8' | k1_relat_1('#skF_6'(A_17))!='#skF_8' | ~v1_funct_1('#skF_6'(A_17)))), inference(resolution, [status(thm)], [c_44, c_207])).
% 9.71/3.46  tff(c_286, plain, (![A_67, A_68]: ('#skF_7'(A_67)='#skF_6'(A_68) | A_67!='#skF_8' | A_68!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_209])).
% 9.71/3.46  tff(c_38, plain, (![A_17, C_22]: (k1_funct_1('#skF_6'(A_17), C_22)=k1_xboole_0 | ~r2_hidden(C_22, A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.71/3.46  tff(c_295, plain, (![A_67, C_22, A_68]: (k1_funct_1('#skF_7'(A_67), C_22)=k1_xboole_0 | ~r2_hidden(C_22, A_68) | A_67!='#skF_8' | A_68!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_286, c_38])).
% 9.71/3.46  tff(c_12992, plain, (![A_393, A_394]: (k1_funct_1('#skF_7'(A_393), '#skF_4'(k1_xboole_0, A_394))=k1_xboole_0 | A_393!='#skF_8' | A_394!='#skF_8' | k1_xboole_0=A_394)), inference(resolution, [status(thm)], [c_11033, c_295])).
% 9.71/3.46  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.71/3.46  tff(c_1399, plain, (![A_138, B_139]: (~v1_xboole_0(A_138) | r2_hidden('#skF_4'(A_138, B_139), B_139) | B_139=A_138)), inference(resolution, [status(thm)], [c_712, c_4])).
% 9.71/3.46  tff(c_211, plain, (![A_54, A_23]: ('#skF_7'(A_54)='#skF_7'(A_23) | A_54!='#skF_8' | k1_relat_1('#skF_7'(A_23))!='#skF_8' | ~v1_funct_1('#skF_7'(A_23)))), inference(resolution, [status(thm)], [c_52, c_207])).
% 9.71/3.46  tff(c_344, plain, (![A_74, A_73]: ('#skF_7'(A_74)='#skF_7'(A_73) | A_73!='#skF_8' | A_74!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_211])).
% 9.71/3.46  tff(c_46, plain, (![A_23, C_28]: (k1_funct_1('#skF_7'(A_23), C_28)=np__1 | ~r2_hidden(C_28, A_23))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.71/3.46  tff(c_368, plain, (![A_73, C_28, A_74]: (k1_funct_1('#skF_7'(A_73), C_28)=np__1 | ~r2_hidden(C_28, A_74) | A_73!='#skF_8' | A_74!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_344, c_46])).
% 9.71/3.46  tff(c_1422, plain, (![A_73, A_138, B_139]: (k1_funct_1('#skF_7'(A_73), '#skF_4'(A_138, B_139))=np__1 | A_73!='#skF_8' | B_139!='#skF_8' | ~v1_xboole_0(A_138) | B_139=A_138)), inference(resolution, [status(thm)], [c_1399, c_368])).
% 9.71/3.46  tff(c_12998, plain, (![A_393, A_394]: (np__1=k1_xboole_0 | A_393!='#skF_8' | A_394!='#skF_8' | ~v1_xboole_0(k1_xboole_0) | k1_xboole_0=A_394 | A_393!='#skF_8' | A_394!='#skF_8' | k1_xboole_0=A_394)), inference(superposition, [status(thm), theory('equality')], [c_12992, c_1422])).
% 9.71/3.46  tff(c_13024, plain, (![A_393, A_394]: (np__1=k1_xboole_0 | A_393!='#skF_8' | A_394!='#skF_8' | k1_xboole_0=A_394)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_12998])).
% 9.71/3.46  tff(c_13028, plain, (![A_393]: (A_393!='#skF_8')), inference(splitLeft, [status(thm)], [c_13024])).
% 9.71/3.46  tff(c_13032, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_13028])).
% 9.71/3.46  tff(c_13033, plain, (![A_394]: (np__1=k1_xboole_0 | A_394!='#skF_8' | k1_xboole_0=A_394)), inference(splitRight, [status(thm)], [c_13024])).
% 9.71/3.46  tff(c_13034, plain, (np__1=k1_xboole_0), inference(splitLeft, [status(thm)], [c_13033])).
% 9.71/3.46  tff(c_54, plain, (~v1_xboole_0(np__1)), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.71/3.46  tff(c_13044, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13034, c_54])).
% 9.71/3.46  tff(c_13047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_13044])).
% 9.71/3.46  tff(c_13320, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_13033])).
% 9.71/3.46  tff(c_56, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.71/3.46  tff(c_13358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13320, c_56])).
% 9.71/3.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.71/3.46  
% 9.71/3.46  Inference rules
% 9.71/3.46  ----------------------
% 9.71/3.46  #Ref     : 7
% 9.71/3.46  #Sup     : 3707
% 9.71/3.46  #Fact    : 0
% 9.71/3.46  #Define  : 0
% 9.71/3.46  #Split   : 8
% 9.71/3.46  #Chain   : 0
% 9.71/3.46  #Close   : 0
% 9.71/3.46  
% 9.71/3.46  Ordering : KBO
% 9.71/3.46  
% 9.71/3.46  Simplification rules
% 9.71/3.46  ----------------------
% 9.71/3.46  #Subsume      : 1479
% 9.71/3.46  #Demod        : 1236
% 9.71/3.46  #Tautology    : 828
% 9.71/3.46  #SimpNegUnit  : 19
% 9.71/3.46  #BackRed      : 55
% 9.71/3.46  
% 9.71/3.46  #Partial instantiations: 0
% 9.71/3.46  #Strategies tried      : 1
% 9.71/3.46  
% 9.71/3.46  Timing (in seconds)
% 9.71/3.46  ----------------------
% 9.71/3.47  Preprocessing        : 0.33
% 9.71/3.47  Parsing              : 0.17
% 9.71/3.47  CNF conversion       : 0.02
% 9.71/3.47  Main loop            : 2.33
% 9.71/3.47  Inferencing          : 0.54
% 9.71/3.47  Reduction            : 0.73
% 9.71/3.47  Demodulation         : 0.58
% 9.71/3.47  BG Simplification    : 0.07
% 9.71/3.47  Subsumption          : 0.86
% 9.71/3.47  Abstraction          : 0.09
% 9.71/3.47  MUC search           : 0.00
% 9.71/3.47  Cooper               : 0.00
% 9.71/3.47  Total                : 2.69
% 9.71/3.47  Index Insertion      : 0.00
% 9.71/3.47  Index Deletion       : 0.00
% 9.71/3.47  Index Matching       : 0.00
% 9.71/3.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
