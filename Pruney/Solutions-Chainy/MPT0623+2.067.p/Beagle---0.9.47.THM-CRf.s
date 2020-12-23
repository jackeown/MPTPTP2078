%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:15 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 139 expanded)
%              Number of leaves         :   28 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  125 ( 351 expanded)
%              Number of equality atoms :   68 ( 188 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_65,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_34,plain,(
    ! [A_12] : v1_relat_1('#skF_3'(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32,plain,(
    ! [A_12] : v1_funct_1('#skF_3'(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_12] : k1_relat_1('#skF_3'(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_46,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_59,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_206,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,B_66),B_66)
      | r2_hidden('#skF_2'(A_65,B_66),A_65)
      | B_66 = A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_82,plain,(
    ! [A_32,B_33] : ~ r2_hidden(A_32,k2_zfmisc_1(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_88,plain,(
    ! [A_7] : ~ r2_hidden(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_82])).

tff(c_220,plain,(
    ! [B_66] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_66),B_66)
      | k1_xboole_0 = B_66 ) ),
    inference(resolution,[status(thm)],[c_206,c_88])).

tff(c_38,plain,(
    ! [A_18,B_22] :
      ( k1_relat_1('#skF_4'(A_18,B_22)) = A_18
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_40,plain,(
    ! [A_18,B_22] :
      ( v1_funct_1('#skF_4'(A_18,B_22))
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    ! [A_18,B_22] :
      ( v1_relat_1('#skF_4'(A_18,B_22))
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k1_tarski(A_5),B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_129,plain,(
    ! [A_49,B_50] :
      ( k2_relat_1('#skF_4'(A_49,B_50)) = k1_tarski(B_50)
      | k1_xboole_0 = A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_44,plain,(
    ! [C_25] :
      ( ~ r1_tarski(k2_relat_1(C_25),'#skF_5')
      | k1_relat_1(C_25) != '#skF_6'
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_201,plain,(
    ! [B_63,A_64] :
      ( ~ r1_tarski(k1_tarski(B_63),'#skF_5')
      | k1_relat_1('#skF_4'(A_64,B_63)) != '#skF_6'
      | ~ v1_funct_1('#skF_4'(A_64,B_63))
      | ~ v1_relat_1('#skF_4'(A_64,B_63))
      | k1_xboole_0 = A_64 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_44])).

tff(c_293,plain,(
    ! [A_79,A_80] :
      ( k1_relat_1('#skF_4'(A_79,A_80)) != '#skF_6'
      | ~ v1_funct_1('#skF_4'(A_79,A_80))
      | ~ v1_relat_1('#skF_4'(A_79,A_80))
      | k1_xboole_0 = A_79
      | ~ r2_hidden(A_80,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14,c_201])).

tff(c_299,plain,(
    ! [A_81,B_82] :
      ( k1_relat_1('#skF_4'(A_81,B_82)) != '#skF_6'
      | ~ v1_funct_1('#skF_4'(A_81,B_82))
      | ~ r2_hidden(B_82,'#skF_5')
      | k1_xboole_0 = A_81 ) ),
    inference(resolution,[status(thm)],[c_42,c_293])).

tff(c_304,plain,(
    ! [A_83,B_84] :
      ( k1_relat_1('#skF_4'(A_83,B_84)) != '#skF_6'
      | ~ r2_hidden(B_84,'#skF_5')
      | k1_xboole_0 = A_83 ) ),
    inference(resolution,[status(thm)],[c_40,c_299])).

tff(c_307,plain,(
    ! [A_18,B_22] :
      ( A_18 != '#skF_6'
      | ~ r2_hidden(B_22,'#skF_5')
      | k1_xboole_0 = A_18
      | k1_xboole_0 = A_18 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_304])).

tff(c_309,plain,(
    ! [B_85] : ~ r2_hidden(B_85,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_313,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_220,c_309])).

tff(c_327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_313])).

tff(c_329,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_153,plain,(
    ! [A_54] :
      ( k2_relat_1(A_54) = k1_xboole_0
      | k1_relat_1(A_54) != k1_xboole_0
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_159,plain,(
    ! [A_12] :
      ( k2_relat_1('#skF_3'(A_12)) = k1_xboole_0
      | k1_relat_1('#skF_3'(A_12)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_153])).

tff(c_164,plain,(
    ! [A_55] :
      ( k2_relat_1('#skF_3'(A_55)) = k1_xboole_0
      | k1_xboole_0 != A_55 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_159])).

tff(c_173,plain,(
    ! [A_55] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_5')
      | k1_relat_1('#skF_3'(A_55)) != '#skF_6'
      | ~ v1_funct_1('#skF_3'(A_55))
      | ~ v1_relat_1('#skF_3'(A_55))
      | k1_xboole_0 != A_55 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_44])).

tff(c_180,plain,(
    ! [A_55] :
      ( A_55 != '#skF_6'
      | k1_xboole_0 != A_55 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_10,c_173])).

tff(c_185,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_180])).

tff(c_355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_185])).

tff(c_356,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_358,plain,(
    ! [A_4] : r1_tarski('#skF_6',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_10])).

tff(c_26,plain,(
    ! [A_11] :
      ( k2_relat_1(A_11) = k1_xboole_0
      | k1_relat_1(A_11) != k1_xboole_0
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_435,plain,(
    ! [A_105] :
      ( k2_relat_1(A_105) = '#skF_6'
      | k1_relat_1(A_105) != '#skF_6'
      | ~ v1_relat_1(A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_356,c_26])).

tff(c_441,plain,(
    ! [A_12] :
      ( k2_relat_1('#skF_3'(A_12)) = '#skF_6'
      | k1_relat_1('#skF_3'(A_12)) != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_34,c_435])).

tff(c_446,plain,(
    ! [A_106] :
      ( k2_relat_1('#skF_3'(A_106)) = '#skF_6'
      | A_106 != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_441])).

tff(c_357,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_363,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_357])).

tff(c_368,plain,(
    ! [C_25] :
      ( ~ r1_tarski(k2_relat_1(C_25),'#skF_6')
      | k1_relat_1(C_25) != '#skF_6'
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_44])).

tff(c_452,plain,(
    ! [A_106] :
      ( ~ r1_tarski('#skF_6','#skF_6')
      | k1_relat_1('#skF_3'(A_106)) != '#skF_6'
      | ~ v1_funct_1('#skF_3'(A_106))
      | ~ v1_relat_1('#skF_3'(A_106))
      | A_106 != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_368])).

tff(c_458,plain,(
    ! [A_106] : A_106 != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_358,c_452])).

tff(c_379,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_356,c_18])).

tff(c_470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.39  
% 2.40/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.39  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 2.40/1.39  
% 2.40/1.39  %Foreground sorts:
% 2.40/1.39  
% 2.40/1.39  
% 2.40/1.39  %Background operators:
% 2.40/1.39  
% 2.40/1.39  
% 2.40/1.39  %Foreground operators:
% 2.40/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.40/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.40/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.40/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.40/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.40/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.40/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.40/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.40/1.39  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.40/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.40/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.40/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.40/1.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.40/1.39  
% 2.40/1.40  tff(f_65, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.40/1.40  tff(f_96, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 2.40/1.40  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.40/1.40  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.40/1.40  tff(f_47, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.40/1.40  tff(f_78, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 2.40/1.40  tff(f_38, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.40/1.40  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.40/1.40  tff(f_53, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.40/1.40  tff(c_34, plain, (![A_12]: (v1_relat_1('#skF_3'(A_12)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.40/1.40  tff(c_32, plain, (![A_12]: (v1_funct_1('#skF_3'(A_12)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.40/1.40  tff(c_30, plain, (![A_12]: (k1_relat_1('#skF_3'(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.40/1.40  tff(c_46, plain, (k1_xboole_0='#skF_6' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.40/1.40  tff(c_59, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_46])).
% 2.40/1.40  tff(c_206, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66), B_66) | r2_hidden('#skF_2'(A_65, B_66), A_65) | B_66=A_65)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.40/1.40  tff(c_18, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.40/1.40  tff(c_82, plain, (![A_32, B_33]: (~r2_hidden(A_32, k2_zfmisc_1(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.40/1.40  tff(c_88, plain, (![A_7]: (~r2_hidden(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_82])).
% 2.40/1.40  tff(c_220, plain, (![B_66]: (r2_hidden('#skF_1'(k1_xboole_0, B_66), B_66) | k1_xboole_0=B_66)), inference(resolution, [status(thm)], [c_206, c_88])).
% 2.40/1.40  tff(c_38, plain, (![A_18, B_22]: (k1_relat_1('#skF_4'(A_18, B_22))=A_18 | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.40/1.40  tff(c_40, plain, (![A_18, B_22]: (v1_funct_1('#skF_4'(A_18, B_22)) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.40/1.40  tff(c_42, plain, (![A_18, B_22]: (v1_relat_1('#skF_4'(A_18, B_22)) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.40/1.40  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(k1_tarski(A_5), B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.40/1.40  tff(c_129, plain, (![A_49, B_50]: (k2_relat_1('#skF_4'(A_49, B_50))=k1_tarski(B_50) | k1_xboole_0=A_49)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.40/1.40  tff(c_44, plain, (![C_25]: (~r1_tarski(k2_relat_1(C_25), '#skF_5') | k1_relat_1(C_25)!='#skF_6' | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.40/1.40  tff(c_201, plain, (![B_63, A_64]: (~r1_tarski(k1_tarski(B_63), '#skF_5') | k1_relat_1('#skF_4'(A_64, B_63))!='#skF_6' | ~v1_funct_1('#skF_4'(A_64, B_63)) | ~v1_relat_1('#skF_4'(A_64, B_63)) | k1_xboole_0=A_64)), inference(superposition, [status(thm), theory('equality')], [c_129, c_44])).
% 2.40/1.40  tff(c_293, plain, (![A_79, A_80]: (k1_relat_1('#skF_4'(A_79, A_80))!='#skF_6' | ~v1_funct_1('#skF_4'(A_79, A_80)) | ~v1_relat_1('#skF_4'(A_79, A_80)) | k1_xboole_0=A_79 | ~r2_hidden(A_80, '#skF_5'))), inference(resolution, [status(thm)], [c_14, c_201])).
% 2.40/1.40  tff(c_299, plain, (![A_81, B_82]: (k1_relat_1('#skF_4'(A_81, B_82))!='#skF_6' | ~v1_funct_1('#skF_4'(A_81, B_82)) | ~r2_hidden(B_82, '#skF_5') | k1_xboole_0=A_81)), inference(resolution, [status(thm)], [c_42, c_293])).
% 2.40/1.40  tff(c_304, plain, (![A_83, B_84]: (k1_relat_1('#skF_4'(A_83, B_84))!='#skF_6' | ~r2_hidden(B_84, '#skF_5') | k1_xboole_0=A_83)), inference(resolution, [status(thm)], [c_40, c_299])).
% 2.40/1.40  tff(c_307, plain, (![A_18, B_22]: (A_18!='#skF_6' | ~r2_hidden(B_22, '#skF_5') | k1_xboole_0=A_18 | k1_xboole_0=A_18)), inference(superposition, [status(thm), theory('equality')], [c_38, c_304])).
% 2.40/1.40  tff(c_309, plain, (![B_85]: (~r2_hidden(B_85, '#skF_5'))), inference(splitLeft, [status(thm)], [c_307])).
% 2.40/1.40  tff(c_313, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_220, c_309])).
% 2.40/1.40  tff(c_327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_313])).
% 2.40/1.40  tff(c_329, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_307])).
% 2.40/1.40  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.40/1.40  tff(c_153, plain, (![A_54]: (k2_relat_1(A_54)=k1_xboole_0 | k1_relat_1(A_54)!=k1_xboole_0 | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.40/1.40  tff(c_159, plain, (![A_12]: (k2_relat_1('#skF_3'(A_12))=k1_xboole_0 | k1_relat_1('#skF_3'(A_12))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_153])).
% 2.40/1.40  tff(c_164, plain, (![A_55]: (k2_relat_1('#skF_3'(A_55))=k1_xboole_0 | k1_xboole_0!=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_159])).
% 2.40/1.40  tff(c_173, plain, (![A_55]: (~r1_tarski(k1_xboole_0, '#skF_5') | k1_relat_1('#skF_3'(A_55))!='#skF_6' | ~v1_funct_1('#skF_3'(A_55)) | ~v1_relat_1('#skF_3'(A_55)) | k1_xboole_0!=A_55)), inference(superposition, [status(thm), theory('equality')], [c_164, c_44])).
% 2.40/1.40  tff(c_180, plain, (![A_55]: (A_55!='#skF_6' | k1_xboole_0!=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_10, c_173])).
% 2.40/1.40  tff(c_185, plain, (k1_xboole_0!='#skF_6'), inference(reflexivity, [status(thm), theory('equality')], [c_180])).
% 2.40/1.40  tff(c_355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_329, c_185])).
% 2.40/1.40  tff(c_356, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_46])).
% 2.40/1.40  tff(c_358, plain, (![A_4]: (r1_tarski('#skF_6', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_356, c_10])).
% 2.40/1.40  tff(c_26, plain, (![A_11]: (k2_relat_1(A_11)=k1_xboole_0 | k1_relat_1(A_11)!=k1_xboole_0 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.40/1.40  tff(c_435, plain, (![A_105]: (k2_relat_1(A_105)='#skF_6' | k1_relat_1(A_105)!='#skF_6' | ~v1_relat_1(A_105))), inference(demodulation, [status(thm), theory('equality')], [c_356, c_356, c_26])).
% 2.40/1.40  tff(c_441, plain, (![A_12]: (k2_relat_1('#skF_3'(A_12))='#skF_6' | k1_relat_1('#skF_3'(A_12))!='#skF_6')), inference(resolution, [status(thm)], [c_34, c_435])).
% 2.40/1.40  tff(c_446, plain, (![A_106]: (k2_relat_1('#skF_3'(A_106))='#skF_6' | A_106!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_441])).
% 2.40/1.40  tff(c_357, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_46])).
% 2.40/1.40  tff(c_363, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_356, c_357])).
% 2.40/1.40  tff(c_368, plain, (![C_25]: (~r1_tarski(k2_relat_1(C_25), '#skF_6') | k1_relat_1(C_25)!='#skF_6' | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_44])).
% 2.40/1.40  tff(c_452, plain, (![A_106]: (~r1_tarski('#skF_6', '#skF_6') | k1_relat_1('#skF_3'(A_106))!='#skF_6' | ~v1_funct_1('#skF_3'(A_106)) | ~v1_relat_1('#skF_3'(A_106)) | A_106!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_446, c_368])).
% 2.40/1.40  tff(c_458, plain, (![A_106]: (A_106!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_358, c_452])).
% 2.40/1.40  tff(c_379, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_356, c_356, c_18])).
% 2.40/1.40  tff(c_470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_458, c_379])).
% 2.40/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.40  
% 2.40/1.40  Inference rules
% 2.40/1.40  ----------------------
% 2.40/1.40  #Ref     : 1
% 2.40/1.40  #Sup     : 77
% 2.40/1.40  #Fact    : 0
% 2.40/1.40  #Define  : 0
% 2.40/1.40  #Split   : 3
% 2.40/1.40  #Chain   : 0
% 2.40/1.40  #Close   : 0
% 2.40/1.40  
% 2.40/1.40  Ordering : KBO
% 2.40/1.40  
% 2.40/1.40  Simplification rules
% 2.40/1.40  ----------------------
% 2.40/1.40  #Subsume      : 14
% 2.40/1.40  #Demod        : 64
% 2.40/1.40  #Tautology    : 48
% 2.40/1.40  #SimpNegUnit  : 13
% 2.40/1.40  #BackRed      : 34
% 2.40/1.40  
% 2.40/1.40  #Partial instantiations: 0
% 2.40/1.40  #Strategies tried      : 1
% 2.40/1.40  
% 2.40/1.40  Timing (in seconds)
% 2.40/1.40  ----------------------
% 2.40/1.41  Preprocessing        : 0.32
% 2.40/1.41  Parsing              : 0.17
% 2.40/1.41  CNF conversion       : 0.02
% 2.40/1.41  Main loop            : 0.26
% 2.40/1.41  Inferencing          : 0.10
% 2.40/1.41  Reduction            : 0.07
% 2.40/1.41  Demodulation         : 0.05
% 2.40/1.41  BG Simplification    : 0.02
% 2.40/1.41  Subsumption          : 0.04
% 2.40/1.41  Abstraction          : 0.01
% 2.40/1.41  MUC search           : 0.00
% 2.40/1.41  Cooper               : 0.00
% 2.40/1.41  Total                : 0.61
% 2.40/1.41  Index Insertion      : 0.00
% 2.40/1.41  Index Deletion       : 0.00
% 2.40/1.41  Index Matching       : 0.00
% 2.40/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
