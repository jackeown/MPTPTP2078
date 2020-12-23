%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:07 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 249 expanded)
%              Number of leaves         :   30 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :  150 ( 596 expanded)
%              Number of equality atoms :   73 ( 341 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_84,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_51,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_46,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_69,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_18,B_22] :
      ( k1_relat_1('#skF_3'(A_18,B_22)) = A_18
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_40,plain,(
    ! [A_18,B_22] :
      ( v1_funct_1('#skF_3'(A_18,B_22))
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,(
    ! [A_18,B_22] :
      ( v1_relat_1('#skF_3'(A_18,B_22))
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k1_tarski(A_8),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_256,plain,(
    ! [A_59,B_60] :
      ( k2_relat_1('#skF_3'(A_59,B_60)) = k1_tarski(B_60)
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,(
    ! [C_25] :
      ( ~ r1_tarski(k2_relat_1(C_25),'#skF_4')
      | k1_relat_1(C_25) != '#skF_5'
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_296,plain,(
    ! [B_66,A_67] :
      ( ~ r1_tarski(k1_tarski(B_66),'#skF_4')
      | k1_relat_1('#skF_3'(A_67,B_66)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_67,B_66))
      | ~ v1_relat_1('#skF_3'(A_67,B_66))
      | k1_xboole_0 = A_67 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_44])).

tff(c_310,plain,(
    ! [A_74,A_75] :
      ( k1_relat_1('#skF_3'(A_74,A_75)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_74,A_75))
      | ~ v1_relat_1('#skF_3'(A_74,A_75))
      | k1_xboole_0 = A_74
      | ~ r2_hidden(A_75,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_296])).

tff(c_315,plain,(
    ! [A_76,B_77] :
      ( k1_relat_1('#skF_3'(A_76,B_77)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_76,B_77))
      | ~ r2_hidden(B_77,'#skF_4')
      | k1_xboole_0 = A_76 ) ),
    inference(resolution,[status(thm)],[c_42,c_310])).

tff(c_320,plain,(
    ! [A_78,B_79] :
      ( k1_relat_1('#skF_3'(A_78,B_79)) != '#skF_5'
      | ~ r2_hidden(B_79,'#skF_4')
      | k1_xboole_0 = A_78 ) ),
    inference(resolution,[status(thm)],[c_40,c_315])).

tff(c_323,plain,(
    ! [A_18,B_22] :
      ( A_18 != '#skF_5'
      | ~ r2_hidden(B_22,'#skF_4')
      | k1_xboole_0 = A_18
      | k1_xboole_0 = A_18 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_320])).

tff(c_325,plain,(
    ! [B_80] : ~ r2_hidden(B_80,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_323])).

tff(c_330,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_325])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_333,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_330,c_8])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_333])).

tff(c_342,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_323])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [A_29] :
      ( v1_relat_1(A_29)
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_62,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_58])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_113,plain,(
    ! [C_43] :
      ( ~ r1_tarski(k2_relat_1(C_43),'#skF_4')
      | k1_relat_1(C_43) != '#skF_5'
      | ~ v1_funct_1(C_43)
      | ~ v1_relat_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_116,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_4')
    | k1_relat_1(k1_xboole_0) != '#skF_5'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_113])).

tff(c_118,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_22,c_10,c_116])).

tff(c_119,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_30,plain,(
    ! [A_12] : k1_relat_1('#skF_2'(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    ! [A_12] : v1_relat_1('#skF_2'(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_135,plain,(
    ! [A_48] :
      ( k1_relat_1(A_48) != k1_xboole_0
      | k1_xboole_0 = A_48
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_144,plain,(
    ! [A_12] :
      ( k1_relat_1('#skF_2'(A_12)) != k1_xboole_0
      | '#skF_2'(A_12) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_135])).

tff(c_162,plain,(
    ! [A_51] :
      ( k1_xboole_0 != A_51
      | '#skF_2'(A_51) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_144])).

tff(c_32,plain,(
    ! [A_12] : v1_funct_1('#skF_2'(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_173,plain,(
    ! [A_51] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_51 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_32])).

tff(c_181,plain,(
    ! [A_51] : k1_xboole_0 != A_51 ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_173])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_20])).

tff(c_195,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_195])).

tff(c_371,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_370,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_382,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_370])).

tff(c_375,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_370,c_22])).

tff(c_417,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_382,c_375])).

tff(c_376,plain,(
    ! [A_6] : r1_tarski('#skF_5',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_10])).

tff(c_415,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_376])).

tff(c_373,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_62])).

tff(c_405,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_373])).

tff(c_374,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_370,c_20])).

tff(c_400,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_382,c_374])).

tff(c_409,plain,(
    ! [C_81] :
      ( ~ r1_tarski(k2_relat_1(C_81),'#skF_4')
      | k1_relat_1(C_81) != '#skF_4'
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_44])).

tff(c_412,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_409])).

tff(c_414,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4'
    | ~ v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_412])).

tff(c_458,plain,(
    ~ v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_415,c_414])).

tff(c_26,plain,(
    ! [A_11] :
      ( k1_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_483,plain,(
    ! [A_98] :
      ( k1_relat_1(A_98) != '#skF_4'
      | A_98 = '#skF_4'
      | ~ v1_relat_1(A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_371,c_26])).

tff(c_492,plain,(
    ! [A_12] :
      ( k1_relat_1('#skF_2'(A_12)) != '#skF_4'
      | '#skF_2'(A_12) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_34,c_483])).

tff(c_501,plain,(
    ! [A_99] :
      ( A_99 != '#skF_4'
      | '#skF_2'(A_99) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_492])).

tff(c_509,plain,(
    ! [A_99] :
      ( v1_funct_1('#skF_4')
      | A_99 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_32])).

tff(c_517,plain,(
    ! [A_99] : A_99 != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_509])).

tff(c_542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_517,c_417])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:41:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.32  
% 2.43/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.33  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 2.43/1.33  
% 2.43/1.33  %Foreground sorts:
% 2.43/1.33  
% 2.43/1.33  
% 2.43/1.33  %Background operators:
% 2.43/1.33  
% 2.43/1.33  
% 2.43/1.33  %Foreground operators:
% 2.43/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.43/1.33  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.43/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.43/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.43/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.43/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.43/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.43/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.43/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.43/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.43/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.43/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.43/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.43/1.33  
% 2.82/1.34  tff(f_102, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 2.82/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.82/1.34  tff(f_84, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 2.82/1.34  tff(f_44, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.82/1.34  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.82/1.34  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.82/1.34  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.82/1.34  tff(f_51, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.82/1.34  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.82/1.34  tff(f_71, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.82/1.34  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.82/1.34  tff(c_46, plain, (k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.82/1.34  tff(c_69, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_46])).
% 2.82/1.34  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.34  tff(c_38, plain, (![A_18, B_22]: (k1_relat_1('#skF_3'(A_18, B_22))=A_18 | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.82/1.34  tff(c_40, plain, (![A_18, B_22]: (v1_funct_1('#skF_3'(A_18, B_22)) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.82/1.34  tff(c_42, plain, (![A_18, B_22]: (v1_relat_1('#skF_3'(A_18, B_22)) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.82/1.34  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(k1_tarski(A_8), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.82/1.34  tff(c_256, plain, (![A_59, B_60]: (k2_relat_1('#skF_3'(A_59, B_60))=k1_tarski(B_60) | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.82/1.34  tff(c_44, plain, (![C_25]: (~r1_tarski(k2_relat_1(C_25), '#skF_4') | k1_relat_1(C_25)!='#skF_5' | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.82/1.34  tff(c_296, plain, (![B_66, A_67]: (~r1_tarski(k1_tarski(B_66), '#skF_4') | k1_relat_1('#skF_3'(A_67, B_66))!='#skF_5' | ~v1_funct_1('#skF_3'(A_67, B_66)) | ~v1_relat_1('#skF_3'(A_67, B_66)) | k1_xboole_0=A_67)), inference(superposition, [status(thm), theory('equality')], [c_256, c_44])).
% 2.82/1.34  tff(c_310, plain, (![A_74, A_75]: (k1_relat_1('#skF_3'(A_74, A_75))!='#skF_5' | ~v1_funct_1('#skF_3'(A_74, A_75)) | ~v1_relat_1('#skF_3'(A_74, A_75)) | k1_xboole_0=A_74 | ~r2_hidden(A_75, '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_296])).
% 2.82/1.34  tff(c_315, plain, (![A_76, B_77]: (k1_relat_1('#skF_3'(A_76, B_77))!='#skF_5' | ~v1_funct_1('#skF_3'(A_76, B_77)) | ~r2_hidden(B_77, '#skF_4') | k1_xboole_0=A_76)), inference(resolution, [status(thm)], [c_42, c_310])).
% 2.82/1.34  tff(c_320, plain, (![A_78, B_79]: (k1_relat_1('#skF_3'(A_78, B_79))!='#skF_5' | ~r2_hidden(B_79, '#skF_4') | k1_xboole_0=A_78)), inference(resolution, [status(thm)], [c_40, c_315])).
% 2.82/1.34  tff(c_323, plain, (![A_18, B_22]: (A_18!='#skF_5' | ~r2_hidden(B_22, '#skF_4') | k1_xboole_0=A_18 | k1_xboole_0=A_18)), inference(superposition, [status(thm), theory('equality')], [c_38, c_320])).
% 2.82/1.34  tff(c_325, plain, (![B_80]: (~r2_hidden(B_80, '#skF_4'))), inference(splitLeft, [status(thm)], [c_323])).
% 2.82/1.34  tff(c_330, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_325])).
% 2.82/1.34  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.82/1.34  tff(c_333, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_330, c_8])).
% 2.82/1.34  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_333])).
% 2.82/1.34  tff(c_342, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_323])).
% 2.82/1.34  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.34  tff(c_58, plain, (![A_29]: (v1_relat_1(A_29) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.82/1.34  tff(c_62, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_58])).
% 2.82/1.34  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.82/1.34  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.82/1.34  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.82/1.34  tff(c_113, plain, (![C_43]: (~r1_tarski(k2_relat_1(C_43), '#skF_4') | k1_relat_1(C_43)!='#skF_5' | ~v1_funct_1(C_43) | ~v1_relat_1(C_43))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.82/1.34  tff(c_116, plain, (~r1_tarski(k1_xboole_0, '#skF_4') | k1_relat_1(k1_xboole_0)!='#skF_5' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_113])).
% 2.82/1.34  tff(c_118, plain, (k1_xboole_0!='#skF_5' | ~v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_22, c_10, c_116])).
% 2.82/1.34  tff(c_119, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_118])).
% 2.82/1.34  tff(c_30, plain, (![A_12]: (k1_relat_1('#skF_2'(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.82/1.34  tff(c_34, plain, (![A_12]: (v1_relat_1('#skF_2'(A_12)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.82/1.34  tff(c_135, plain, (![A_48]: (k1_relat_1(A_48)!=k1_xboole_0 | k1_xboole_0=A_48 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.82/1.34  tff(c_144, plain, (![A_12]: (k1_relat_1('#skF_2'(A_12))!=k1_xboole_0 | '#skF_2'(A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_135])).
% 2.82/1.34  tff(c_162, plain, (![A_51]: (k1_xboole_0!=A_51 | '#skF_2'(A_51)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_144])).
% 2.82/1.34  tff(c_32, plain, (![A_12]: (v1_funct_1('#skF_2'(A_12)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.82/1.34  tff(c_173, plain, (![A_51]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_51)), inference(superposition, [status(thm), theory('equality')], [c_162, c_32])).
% 2.82/1.34  tff(c_181, plain, (![A_51]: (k1_xboole_0!=A_51)), inference(negUnitSimplification, [status(thm)], [c_119, c_173])).
% 2.82/1.34  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_181, c_20])).
% 2.82/1.34  tff(c_195, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_118])).
% 2.82/1.34  tff(c_369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_342, c_195])).
% 2.82/1.34  tff(c_371, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 2.82/1.34  tff(c_370, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_46])).
% 2.82/1.34  tff(c_382, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_371, c_370])).
% 2.82/1.34  tff(c_375, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_370, c_370, c_22])).
% 2.82/1.34  tff(c_417, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_382, c_382, c_375])).
% 2.82/1.34  tff(c_376, plain, (![A_6]: (r1_tarski('#skF_5', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_370, c_10])).
% 2.82/1.34  tff(c_415, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_382, c_376])).
% 2.82/1.34  tff(c_373, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_370, c_62])).
% 2.82/1.34  tff(c_405, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_382, c_373])).
% 2.82/1.34  tff(c_374, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_370, c_370, c_20])).
% 2.82/1.34  tff(c_400, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_382, c_382, c_374])).
% 2.82/1.34  tff(c_409, plain, (![C_81]: (~r1_tarski(k2_relat_1(C_81), '#skF_4') | k1_relat_1(C_81)!='#skF_4' | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(demodulation, [status(thm), theory('equality')], [c_382, c_44])).
% 2.82/1.34  tff(c_412, plain, (~r1_tarski('#skF_4', '#skF_4') | k1_relat_1('#skF_4')!='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_400, c_409])).
% 2.82/1.34  tff(c_414, plain, (~r1_tarski('#skF_4', '#skF_4') | k1_relat_1('#skF_4')!='#skF_4' | ~v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_405, c_412])).
% 2.82/1.34  tff(c_458, plain, (~v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_417, c_415, c_414])).
% 2.82/1.34  tff(c_26, plain, (![A_11]: (k1_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.82/1.34  tff(c_483, plain, (![A_98]: (k1_relat_1(A_98)!='#skF_4' | A_98='#skF_4' | ~v1_relat_1(A_98))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_371, c_26])).
% 2.82/1.34  tff(c_492, plain, (![A_12]: (k1_relat_1('#skF_2'(A_12))!='#skF_4' | '#skF_2'(A_12)='#skF_4')), inference(resolution, [status(thm)], [c_34, c_483])).
% 2.82/1.34  tff(c_501, plain, (![A_99]: (A_99!='#skF_4' | '#skF_2'(A_99)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_492])).
% 2.82/1.35  tff(c_509, plain, (![A_99]: (v1_funct_1('#skF_4') | A_99!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_501, c_32])).
% 2.82/1.35  tff(c_517, plain, (![A_99]: (A_99!='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_458, c_509])).
% 2.82/1.35  tff(c_542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_517, c_417])).
% 2.82/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.35  
% 2.82/1.35  Inference rules
% 2.82/1.35  ----------------------
% 2.82/1.35  #Ref     : 0
% 2.82/1.35  #Sup     : 92
% 2.82/1.35  #Fact    : 0
% 2.82/1.35  #Define  : 0
% 2.82/1.35  #Split   : 3
% 2.82/1.35  #Chain   : 0
% 2.82/1.35  #Close   : 0
% 2.82/1.35  
% 2.82/1.35  Ordering : KBO
% 2.82/1.35  
% 2.82/1.35  Simplification rules
% 2.82/1.35  ----------------------
% 2.82/1.35  #Subsume      : 12
% 2.82/1.35  #Demod        : 92
% 2.82/1.35  #Tautology    : 64
% 2.82/1.35  #SimpNegUnit  : 24
% 2.82/1.35  #BackRed      : 48
% 2.82/1.35  
% 2.82/1.35  #Partial instantiations: 0
% 2.82/1.35  #Strategies tried      : 1
% 2.82/1.35  
% 2.82/1.35  Timing (in seconds)
% 2.82/1.35  ----------------------
% 2.82/1.35  Preprocessing        : 0.30
% 2.82/1.35  Parsing              : 0.16
% 2.82/1.35  CNF conversion       : 0.02
% 2.82/1.35  Main loop            : 0.26
% 2.82/1.35  Inferencing          : 0.10
% 2.82/1.35  Reduction            : 0.08
% 2.82/1.35  Demodulation         : 0.05
% 2.82/1.35  BG Simplification    : 0.02
% 2.82/1.35  Subsumption          : 0.04
% 2.82/1.35  Abstraction          : 0.01
% 2.82/1.35  MUC search           : 0.00
% 2.82/1.35  Cooper               : 0.00
% 2.82/1.35  Total                : 0.60
% 2.82/1.35  Index Insertion      : 0.00
% 2.82/1.35  Index Deletion       : 0.00
% 2.82/1.35  Index Matching       : 0.00
% 2.82/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
