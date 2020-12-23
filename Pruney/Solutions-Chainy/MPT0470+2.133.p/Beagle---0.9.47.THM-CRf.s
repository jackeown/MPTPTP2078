%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:19 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 114 expanded)
%              Number of leaves         :   36 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  102 ( 174 expanded)
%              Number of equality atoms :   38 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_93,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_44,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_87,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_46,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_1'(A_25),A_25)
      | v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [A_67,C_68,B_69] :
      ( ~ r2_hidden(A_67,C_68)
      | ~ r1_xboole_0(k2_tarski(A_67,B_69),C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_124,plain,(
    ! [A_70] : ~ r2_hidden(A_70,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_118])).

tff(c_129,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_124])).

tff(c_32,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1(k5_relat_1(A_43,B_44))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [B_19] : k2_zfmisc_1(k1_xboole_0,B_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_232,plain,(
    ! [A_97,B_98] :
      ( k1_relat_1(k5_relat_1(A_97,B_98)) = k1_relat_1(A_97)
      | ~ r1_tarski(k2_relat_1(A_97),k1_relat_1(B_98))
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_241,plain,(
    ! [B_98] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_98)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_98))
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_232])).

tff(c_289,plain,(
    ! [B_100] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_100)) = k1_xboole_0
      | ~ v1_relat_1(B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_4,c_42,c_241])).

tff(c_34,plain,(
    ! [A_45] :
      ( k3_xboole_0(A_45,k2_zfmisc_1(k1_relat_1(A_45),k2_relat_1(A_45))) = A_45
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_301,plain,(
    ! [B_100] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_100),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_100)))) = k5_relat_1(k1_xboole_0,B_100)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_100))
      | ~ v1_relat_1(B_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_34])).

tff(c_315,plain,(
    ! [B_101] :
      ( k5_relat_1(k1_xboole_0,B_101) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_101))
      | ~ v1_relat_1(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20,c_301])).

tff(c_322,plain,(
    ! [B_44] :
      ( k5_relat_1(k1_xboole_0,B_44) = k1_xboole_0
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_315])).

tff(c_339,plain,(
    ! [B_103] :
      ( k5_relat_1(k1_xboole_0,B_103) = k1_xboole_0
      | ~ v1_relat_1(B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_322])).

tff(c_348,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_339])).

tff(c_355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_348])).

tff(c_356,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_398,plain,(
    ! [A_115,C_116,B_117] :
      ( ~ r2_hidden(A_115,C_116)
      | ~ r1_xboole_0(k2_tarski(A_115,B_117),C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_413,plain,(
    ! [A_121] : ~ r2_hidden(A_121,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_398])).

tff(c_418,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_413])).

tff(c_18,plain,(
    ! [A_18] : k2_zfmisc_1(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_476,plain,(
    ! [B_139,A_140] :
      ( k2_relat_1(k5_relat_1(B_139,A_140)) = k2_relat_1(A_140)
      | ~ r1_tarski(k1_relat_1(A_140),k2_relat_1(B_139))
      | ~ v1_relat_1(B_139)
      | ~ v1_relat_1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_479,plain,(
    ! [B_139] :
      ( k2_relat_1(k5_relat_1(B_139,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_139))
      | ~ v1_relat_1(B_139)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_476])).

tff(c_498,plain,(
    ! [B_143] :
      ( k2_relat_1(k5_relat_1(B_143,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_4,c_40,c_479])).

tff(c_510,plain,(
    ! [B_143] :
      ( k3_xboole_0(k5_relat_1(B_143,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_143,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_143,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_143,k1_xboole_0))
      | ~ v1_relat_1(B_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_34])).

tff(c_545,plain,(
    ! [B_145] :
      ( k5_relat_1(B_145,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_145,k1_xboole_0))
      | ~ v1_relat_1(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18,c_510])).

tff(c_549,plain,(
    ! [A_43] :
      ( k5_relat_1(A_43,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_32,c_545])).

tff(c_588,plain,(
    ! [A_148] :
      ( k5_relat_1(A_148,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_549])).

tff(c_597,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_588])).

tff(c_603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_356,c_597])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.36  
% 2.64/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.64/1.37  
% 2.64/1.37  %Foreground sorts:
% 2.64/1.37  
% 2.64/1.37  
% 2.64/1.37  %Background operators:
% 2.64/1.37  
% 2.64/1.37  
% 2.64/1.37  %Foreground operators:
% 2.64/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.64/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.64/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.64/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.64/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.64/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.64/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.64/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.64/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.64/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.64/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.64/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.64/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.64/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.64/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.64/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.64/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.64/1.37  
% 2.64/1.38  tff(f_100, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.64/1.38  tff(f_62, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.64/1.38  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.64/1.38  tff(f_50, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.64/1.38  tff(f_68, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.64/1.38  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.64/1.38  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.64/1.38  tff(f_29, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.64/1.38  tff(f_93, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.64/1.38  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.64/1.38  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 2.64/1.38  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.64/1.38  tff(c_44, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.64/1.38  tff(c_87, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44])).
% 2.64/1.38  tff(c_46, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.64/1.38  tff(c_30, plain, (![A_25]: (r2_hidden('#skF_1'(A_25), A_25) | v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.64/1.38  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.38  tff(c_118, plain, (![A_67, C_68, B_69]: (~r2_hidden(A_67, C_68) | ~r1_xboole_0(k2_tarski(A_67, B_69), C_68))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.64/1.38  tff(c_124, plain, (![A_70]: (~r2_hidden(A_70, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_118])).
% 2.64/1.38  tff(c_129, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_124])).
% 2.64/1.38  tff(c_32, plain, (![A_43, B_44]: (v1_relat_1(k5_relat_1(A_43, B_44)) | ~v1_relat_1(B_44) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.64/1.38  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.64/1.38  tff(c_20, plain, (![B_19]: (k2_zfmisc_1(k1_xboole_0, B_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.64/1.38  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.64/1.38  tff(c_42, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.64/1.38  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.64/1.38  tff(c_232, plain, (![A_97, B_98]: (k1_relat_1(k5_relat_1(A_97, B_98))=k1_relat_1(A_97) | ~r1_tarski(k2_relat_1(A_97), k1_relat_1(B_98)) | ~v1_relat_1(B_98) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.64/1.38  tff(c_241, plain, (![B_98]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_98))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_98)) | ~v1_relat_1(B_98) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_232])).
% 2.64/1.38  tff(c_289, plain, (![B_100]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_100))=k1_xboole_0 | ~v1_relat_1(B_100))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_4, c_42, c_241])).
% 2.64/1.38  tff(c_34, plain, (![A_45]: (k3_xboole_0(A_45, k2_zfmisc_1(k1_relat_1(A_45), k2_relat_1(A_45)))=A_45 | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.64/1.38  tff(c_301, plain, (![B_100]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_100), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_100))))=k5_relat_1(k1_xboole_0, B_100) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_100)) | ~v1_relat_1(B_100))), inference(superposition, [status(thm), theory('equality')], [c_289, c_34])).
% 2.64/1.38  tff(c_315, plain, (![B_101]: (k5_relat_1(k1_xboole_0, B_101)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_101)) | ~v1_relat_1(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20, c_301])).
% 2.64/1.38  tff(c_322, plain, (![B_44]: (k5_relat_1(k1_xboole_0, B_44)=k1_xboole_0 | ~v1_relat_1(B_44) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_315])).
% 2.64/1.38  tff(c_339, plain, (![B_103]: (k5_relat_1(k1_xboole_0, B_103)=k1_xboole_0 | ~v1_relat_1(B_103))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_322])).
% 2.64/1.38  tff(c_348, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_339])).
% 2.64/1.38  tff(c_355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_348])).
% 2.64/1.38  tff(c_356, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 2.64/1.38  tff(c_398, plain, (![A_115, C_116, B_117]: (~r2_hidden(A_115, C_116) | ~r1_xboole_0(k2_tarski(A_115, B_117), C_116))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.64/1.38  tff(c_413, plain, (![A_121]: (~r2_hidden(A_121, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_398])).
% 2.64/1.38  tff(c_418, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_413])).
% 2.64/1.38  tff(c_18, plain, (![A_18]: (k2_zfmisc_1(A_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.64/1.38  tff(c_476, plain, (![B_139, A_140]: (k2_relat_1(k5_relat_1(B_139, A_140))=k2_relat_1(A_140) | ~r1_tarski(k1_relat_1(A_140), k2_relat_1(B_139)) | ~v1_relat_1(B_139) | ~v1_relat_1(A_140))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.64/1.38  tff(c_479, plain, (![B_139]: (k2_relat_1(k5_relat_1(B_139, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_139)) | ~v1_relat_1(B_139) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_476])).
% 2.64/1.38  tff(c_498, plain, (![B_143]: (k2_relat_1(k5_relat_1(B_143, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_143))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_4, c_40, c_479])).
% 2.64/1.38  tff(c_510, plain, (![B_143]: (k3_xboole_0(k5_relat_1(B_143, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_143, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_143, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_143, k1_xboole_0)) | ~v1_relat_1(B_143))), inference(superposition, [status(thm), theory('equality')], [c_498, c_34])).
% 2.64/1.38  tff(c_545, plain, (![B_145]: (k5_relat_1(B_145, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_145, k1_xboole_0)) | ~v1_relat_1(B_145))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18, c_510])).
% 2.64/1.38  tff(c_549, plain, (![A_43]: (k5_relat_1(A_43, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_43))), inference(resolution, [status(thm)], [c_32, c_545])).
% 2.64/1.38  tff(c_588, plain, (![A_148]: (k5_relat_1(A_148, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_148))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_549])).
% 2.64/1.38  tff(c_597, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_588])).
% 2.64/1.38  tff(c_603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_356, c_597])).
% 2.64/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.38  
% 2.64/1.38  Inference rules
% 2.64/1.38  ----------------------
% 2.64/1.38  #Ref     : 2
% 2.64/1.38  #Sup     : 120
% 2.64/1.38  #Fact    : 0
% 2.64/1.38  #Define  : 0
% 2.64/1.38  #Split   : 1
% 2.64/1.38  #Chain   : 0
% 2.64/1.38  #Close   : 0
% 2.64/1.38  
% 2.64/1.38  Ordering : KBO
% 2.64/1.38  
% 2.64/1.38  Simplification rules
% 2.64/1.38  ----------------------
% 2.64/1.38  #Subsume      : 3
% 2.64/1.38  #Demod        : 81
% 2.64/1.38  #Tautology    : 78
% 2.64/1.38  #SimpNegUnit  : 2
% 2.64/1.38  #BackRed      : 0
% 2.64/1.38  
% 2.64/1.38  #Partial instantiations: 0
% 2.64/1.38  #Strategies tried      : 1
% 2.64/1.38  
% 2.64/1.38  Timing (in seconds)
% 2.64/1.38  ----------------------
% 2.64/1.38  Preprocessing        : 0.31
% 2.64/1.38  Parsing              : 0.16
% 2.64/1.38  CNF conversion       : 0.02
% 2.64/1.38  Main loop            : 0.27
% 2.64/1.38  Inferencing          : 0.11
% 2.64/1.38  Reduction            : 0.08
% 2.64/1.38  Demodulation         : 0.06
% 2.64/1.38  BG Simplification    : 0.02
% 2.64/1.38  Subsumption          : 0.04
% 2.64/1.38  Abstraction          : 0.02
% 2.64/1.38  MUC search           : 0.00
% 2.64/1.38  Cooper               : 0.00
% 2.64/1.38  Total                : 0.61
% 2.64/1.38  Index Insertion      : 0.00
% 2.64/1.38  Index Deletion       : 0.00
% 2.64/1.39  Index Matching       : 0.00
% 2.64/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
