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
% DateTime   : Thu Dec  3 10:25:31 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   76 (  82 expanded)
%              Number of leaves         :   48 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 (  90 expanded)
%              Number of equality atoms :   38 (  47 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > g1_orders_2 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k3_lattice3 > k2_yellow_1 > k2_relat_1 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_lattice3 > o_0_0_xboole_0 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_76,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ~ ( ~ ( A = k1_xboole_0
            & B != k1_xboole_0 )
        & ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ~ ( B = k1_relat_1(C)
                & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_44,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_103,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_116,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_119,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_54,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_66,plain,(
    ! [A_32] : k1_relat_1('#skF_3'(A_32,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_74,plain,(
    ! [A_32] : v1_relat_1('#skF_3'(A_32,k1_xboole_0)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_368,plain,(
    ! [A_75] :
      ( k1_relat_1(A_75) != k1_xboole_0
      | k1_xboole_0 = A_75
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_374,plain,(
    ! [A_32] :
      ( k1_relat_1('#skF_3'(A_32,k1_xboole_0)) != k1_xboole_0
      | '#skF_3'(A_32,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74,c_368])).

tff(c_378,plain,(
    ! [A_32] : '#skF_3'(A_32,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_374])).

tff(c_62,plain,(
    ! [A_32] : r1_tarski(k2_relat_1('#skF_3'(A_32,k1_xboole_0)),A_32) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_379,plain,(
    ! [A_32] : r1_tarski(k2_relat_1(k1_xboole_0),A_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_62])).

tff(c_383,plain,(
    ! [A_32] : r1_tarski(k1_xboole_0,A_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_379])).

tff(c_18,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_292,plain,(
    ! [C_62,B_63] : ~ r2_hidden(C_62,k4_xboole_0(B_63,k1_tarski(C_62))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_295,plain,(
    ! [C_62] : ~ r2_hidden(C_62,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_292])).

tff(c_12,plain,(
    ! [B_5] : r1_tarski(B_5,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,(
    ! [A_26] : k3_tarski(k1_zfmisc_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_78,plain,(
    ! [A_35] : k9_setfam_1(A_35) = k1_zfmisc_1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_86,plain,(
    ! [A_39] : k2_yellow_1(k9_setfam_1(A_39)) = k3_yellow_1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_89,plain,(
    ! [A_39] : k2_yellow_1(k1_zfmisc_1(A_39)) = k3_yellow_1(A_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_86])).

tff(c_30,plain,(
    ! [C_22,A_18] :
      ( r2_hidden(C_22,k1_zfmisc_1(A_18))
      | ~ r1_tarski(C_22,A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_785,plain,(
    ! [A_109] :
      ( k4_yellow_0(k2_yellow_1(A_109)) = k3_tarski(A_109)
      | ~ r2_hidden(k3_tarski(A_109),A_109)
      | v1_xboole_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_797,plain,(
    ! [A_18] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_18))) = k3_tarski(k1_zfmisc_1(A_18))
      | v1_xboole_0(k1_zfmisc_1(A_18))
      | ~ r1_tarski(k3_tarski(k1_zfmisc_1(A_18)),A_18) ) ),
    inference(resolution,[status(thm)],[c_30,c_785])).

tff(c_813,plain,(
    ! [A_110] :
      ( k4_yellow_0(k3_yellow_1(A_110)) = A_110
      | v1_xboole_0(k1_zfmisc_1(A_110)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_48,c_89,c_48,c_797])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_936,plain,(
    ! [A_116] :
      ( k1_zfmisc_1(A_116) = k1_xboole_0
      | k4_yellow_0(k3_yellow_1(A_116)) = A_116 ) ),
    inference(resolution,[status(thm)],[c_813,c_6])).

tff(c_88,plain,(
    k4_yellow_0(k3_yellow_1('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_955,plain,(
    k1_zfmisc_1('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_936,c_88])).

tff(c_965,plain,(
    ! [C_22] :
      ( r2_hidden(C_22,k1_xboole_0)
      | ~ r1_tarski(C_22,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_955,c_30])).

tff(c_993,plain,(
    ! [C_117] : ~ r1_tarski(C_117,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_965])).

tff(c_1006,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_383,c_993])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:56:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.54  
% 3.29/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.54  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > g1_orders_2 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k3_lattice3 > k2_yellow_1 > k2_relat_1 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_lattice3 > o_0_0_xboole_0 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.29/1.54  
% 3.29/1.54  %Foreground sorts:
% 3.29/1.54  
% 3.29/1.54  
% 3.29/1.54  %Background operators:
% 3.29/1.54  
% 3.29/1.54  
% 3.29/1.54  %Foreground operators:
% 3.29/1.54  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.29/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.29/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.54  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.29/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.29/1.54  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.29/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.29/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.54  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.29/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.29/1.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.29/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.29/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.29/1.54  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 3.29/1.54  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 3.29/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.29/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.29/1.54  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.29/1.54  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.29/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.29/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.29/1.54  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 3.29/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.54  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.29/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.29/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.29/1.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.29/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.29/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.29/1.54  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.29/1.54  
% 3.42/1.55  tff(f_76, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.42/1.55  tff(f_101, axiom, (![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 3.42/1.55  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.42/1.55  tff(f_44, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.42/1.55  tff(f_67, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.42/1.55  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.42/1.55  tff(f_69, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.42/1.55  tff(f_103, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 3.42/1.55  tff(f_116, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 3.42/1.55  tff(f_59, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.42/1.55  tff(f_114, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 3.42/1.55  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.42/1.55  tff(f_119, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_yellow_1)).
% 3.42/1.55  tff(c_54, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.42/1.55  tff(c_66, plain, (![A_32]: (k1_relat_1('#skF_3'(A_32, k1_xboole_0))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.42/1.55  tff(c_74, plain, (![A_32]: (v1_relat_1('#skF_3'(A_32, k1_xboole_0)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.42/1.55  tff(c_368, plain, (![A_75]: (k1_relat_1(A_75)!=k1_xboole_0 | k1_xboole_0=A_75 | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.42/1.55  tff(c_374, plain, (![A_32]: (k1_relat_1('#skF_3'(A_32, k1_xboole_0))!=k1_xboole_0 | '#skF_3'(A_32, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_368])).
% 3.42/1.55  tff(c_378, plain, (![A_32]: ('#skF_3'(A_32, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_374])).
% 3.42/1.55  tff(c_62, plain, (![A_32]: (r1_tarski(k2_relat_1('#skF_3'(A_32, k1_xboole_0)), A_32))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.42/1.55  tff(c_379, plain, (![A_32]: (r1_tarski(k2_relat_1(k1_xboole_0), A_32))), inference(demodulation, [status(thm), theory('equality')], [c_378, c_62])).
% 3.42/1.55  tff(c_383, plain, (![A_32]: (r1_tarski(k1_xboole_0, A_32))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_379])).
% 3.42/1.55  tff(c_18, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.42/1.55  tff(c_292, plain, (![C_62, B_63]: (~r2_hidden(C_62, k4_xboole_0(B_63, k1_tarski(C_62))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.42/1.55  tff(c_295, plain, (![C_62]: (~r2_hidden(C_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_292])).
% 3.42/1.55  tff(c_12, plain, (![B_5]: (r1_tarski(B_5, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.42/1.55  tff(c_48, plain, (![A_26]: (k3_tarski(k1_zfmisc_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.42/1.55  tff(c_78, plain, (![A_35]: (k9_setfam_1(A_35)=k1_zfmisc_1(A_35))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.42/1.55  tff(c_86, plain, (![A_39]: (k2_yellow_1(k9_setfam_1(A_39))=k3_yellow_1(A_39))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.42/1.55  tff(c_89, plain, (![A_39]: (k2_yellow_1(k1_zfmisc_1(A_39))=k3_yellow_1(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_86])).
% 3.42/1.55  tff(c_30, plain, (![C_22, A_18]: (r2_hidden(C_22, k1_zfmisc_1(A_18)) | ~r1_tarski(C_22, A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.42/1.55  tff(c_785, plain, (![A_109]: (k4_yellow_0(k2_yellow_1(A_109))=k3_tarski(A_109) | ~r2_hidden(k3_tarski(A_109), A_109) | v1_xboole_0(A_109))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.42/1.55  tff(c_797, plain, (![A_18]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_18)))=k3_tarski(k1_zfmisc_1(A_18)) | v1_xboole_0(k1_zfmisc_1(A_18)) | ~r1_tarski(k3_tarski(k1_zfmisc_1(A_18)), A_18))), inference(resolution, [status(thm)], [c_30, c_785])).
% 3.42/1.55  tff(c_813, plain, (![A_110]: (k4_yellow_0(k3_yellow_1(A_110))=A_110 | v1_xboole_0(k1_zfmisc_1(A_110)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_48, c_89, c_48, c_797])).
% 3.42/1.55  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.42/1.55  tff(c_936, plain, (![A_116]: (k1_zfmisc_1(A_116)=k1_xboole_0 | k4_yellow_0(k3_yellow_1(A_116))=A_116)), inference(resolution, [status(thm)], [c_813, c_6])).
% 3.42/1.55  tff(c_88, plain, (k4_yellow_0(k3_yellow_1('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.42/1.55  tff(c_955, plain, (k1_zfmisc_1('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_936, c_88])).
% 3.42/1.55  tff(c_965, plain, (![C_22]: (r2_hidden(C_22, k1_xboole_0) | ~r1_tarski(C_22, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_955, c_30])).
% 3.42/1.55  tff(c_993, plain, (![C_117]: (~r1_tarski(C_117, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_295, c_965])).
% 3.42/1.55  tff(c_1006, plain, $false, inference(resolution, [status(thm)], [c_383, c_993])).
% 3.42/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.55  
% 3.42/1.55  Inference rules
% 3.42/1.55  ----------------------
% 3.42/1.55  #Ref     : 0
% 3.42/1.55  #Sup     : 211
% 3.42/1.55  #Fact    : 0
% 3.42/1.55  #Define  : 0
% 3.42/1.55  #Split   : 1
% 3.42/1.55  #Chain   : 0
% 3.42/1.55  #Close   : 0
% 3.42/1.55  
% 3.42/1.55  Ordering : KBO
% 3.42/1.55  
% 3.42/1.55  Simplification rules
% 3.42/1.55  ----------------------
% 3.42/1.55  #Subsume      : 8
% 3.42/1.55  #Demod        : 114
% 3.42/1.55  #Tautology    : 154
% 3.42/1.55  #SimpNegUnit  : 6
% 3.42/1.55  #BackRed      : 10
% 3.42/1.55  
% 3.42/1.55  #Partial instantiations: 0
% 3.42/1.55  #Strategies tried      : 1
% 3.42/1.55  
% 3.42/1.55  Timing (in seconds)
% 3.42/1.55  ----------------------
% 3.42/1.56  Preprocessing        : 0.37
% 3.42/1.56  Parsing              : 0.19
% 3.42/1.56  CNF conversion       : 0.02
% 3.42/1.56  Main loop            : 0.36
% 3.42/1.56  Inferencing          : 0.13
% 3.42/1.56  Reduction            : 0.13
% 3.42/1.56  Demodulation         : 0.09
% 3.42/1.56  BG Simplification    : 0.02
% 3.42/1.56  Subsumption          : 0.05
% 3.42/1.56  Abstraction          : 0.02
% 3.42/1.56  MUC search           : 0.00
% 3.42/1.56  Cooper               : 0.00
% 3.42/1.56  Total                : 0.75
% 3.42/1.56  Index Insertion      : 0.00
% 3.42/1.56  Index Deletion       : 0.00
% 3.42/1.56  Index Matching       : 0.00
% 3.42/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
