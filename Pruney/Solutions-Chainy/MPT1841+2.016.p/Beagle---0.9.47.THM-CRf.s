%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:30 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 100 expanded)
%              Number of leaves         :   41 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  104 ( 150 expanded)
%              Number of equality atoms :   31 (  35 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_102,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_74,plain,(
    ! [A_43] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_121,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(A_71,B_72)
      | ~ m1_subset_1(A_71,k1_zfmisc_1(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_129,plain,(
    ! [A_43] : r1_tarski(k1_xboole_0,A_43) ),
    inference(resolution,[status(thm)],[c_74,c_121])).

tff(c_98,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_92,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_96,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_165,plain,(
    ! [A_83,B_84] :
      ( k6_domain_1(A_83,B_84) = k1_tarski(B_84)
      | ~ m1_subset_1(B_84,A_83)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_174,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_165])).

tff(c_179,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_174])).

tff(c_94,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_180,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_94])).

tff(c_244,plain,(
    ! [A_123,B_124] :
      ( m1_subset_1(k6_domain_1(A_123,B_124),k1_zfmisc_1(A_123))
      | ~ m1_subset_1(B_124,A_123)
      | v1_xboole_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_261,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_244])).

tff(c_269,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_261])).

tff(c_270,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_269])).

tff(c_941,plain,(
    ! [B_343,A_344] :
      ( ~ v1_subset_1(B_343,A_344)
      | v1_xboole_0(B_343)
      | ~ m1_subset_1(B_343,k1_zfmisc_1(A_344))
      | ~ v1_zfmisc_1(A_344)
      | v1_xboole_0(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_950,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_270,c_941])).

tff(c_968,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_180,c_950])).

tff(c_969,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_968])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_109,plain,(
    ! [B_64,A_65] :
      ( ~ v1_xboole_0(B_64)
      | B_64 = A_65
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_112,plain,(
    ! [A_65] :
      ( k1_xboole_0 = A_65
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_2,c_109])).

tff(c_979,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_969,c_112])).

tff(c_6,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_4,B_5] : k1_enumset1(A_4,A_4,B_5) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] : k2_enumset1(A_6,A_6,B_7,C_8) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11,D_12] : k3_enumset1(A_9,A_9,B_10,C_11,D_12) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k4_enumset1(A_13,A_13,B_14,C_15,D_16,E_17) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] : k5_enumset1(A_18,A_18,B_19,C_20,D_21,E_22,F_23) = k4_enumset1(A_18,B_19,C_20,D_21,E_22,F_23) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1082,plain,(
    ! [C_421,G_420,D_426,F_424,B_422,A_425,E_423] : k6_enumset1(A_425,A_425,B_422,C_421,D_426,E_423,F_424,G_420) = k5_enumset1(A_425,B_422,C_421,D_426,E_423,F_424,G_420) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    ! [A_31,C_33,B_32,H_38,F_36,E_35,D_34,J_42] : r2_hidden(J_42,k6_enumset1(A_31,B_32,C_33,D_34,E_35,F_36,J_42,H_38)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1193,plain,(
    ! [E_430,F_434,D_432,C_428,A_429,B_433,G_431] : r2_hidden(F_434,k5_enumset1(A_429,B_433,C_428,D_432,E_430,F_434,G_431)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1082,c_24])).

tff(c_1204,plain,(
    ! [D_439,B_440,C_436,F_438,E_437,A_435] : r2_hidden(E_437,k4_enumset1(A_435,B_440,C_436,D_439,E_437,F_438)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1193])).

tff(c_1224,plain,(
    ! [C_446,A_445,E_444,B_443,D_442] : r2_hidden(D_442,k3_enumset1(A_445,B_443,C_446,D_442,E_444)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1204])).

tff(c_1235,plain,(
    ! [C_447,A_448,B_449,D_450] : r2_hidden(C_447,k2_enumset1(A_448,B_449,C_447,D_450)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1224])).

tff(c_1246,plain,(
    ! [B_451,A_452,C_453] : r2_hidden(B_451,k1_enumset1(A_452,B_451,C_453)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1235])).

tff(c_1257,plain,(
    ! [A_454,B_455] : r2_hidden(A_454,k2_tarski(A_454,B_455)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1246])).

tff(c_1268,plain,(
    ! [A_456] : r2_hidden(A_456,k1_tarski(A_456)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1257])).

tff(c_1280,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_1268])).

tff(c_84,plain,(
    ! [B_53,A_52] :
      ( ~ r1_tarski(B_53,A_52)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1335,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_1280,c_84])).

tff(c_1343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_1335])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n006.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 18:23:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.76/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.54  
% 3.76/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.55  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.83/1.55  
% 3.83/1.55  %Foreground sorts:
% 3.83/1.55  
% 3.83/1.55  
% 3.83/1.55  %Background operators:
% 3.83/1.55  
% 3.83/1.55  
% 3.83/1.55  %Foreground operators:
% 3.83/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.83/1.55  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.83/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.83/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.83/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.83/1.55  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.83/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.83/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.83/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.83/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.83/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.83/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.83/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.83/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.83/1.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.83/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.83/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/1.55  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.83/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.83/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.83/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.83/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.83/1.55  
% 3.83/1.56  tff(f_80, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.83/1.56  tff(f_91, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.83/1.56  tff(f_142, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 3.83/1.56  tff(f_116, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.83/1.56  tff(f_109, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.83/1.56  tff(f_130, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.83/1.56  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.83/1.56  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 3.83/1.56  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.83/1.56  tff(f_38, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.83/1.56  tff(f_40, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.83/1.56  tff(f_42, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.83/1.56  tff(f_44, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.83/1.56  tff(f_46, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.83/1.56  tff(f_48, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.83/1.56  tff(f_78, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 3.83/1.56  tff(f_102, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.83/1.56  tff(c_74, plain, (![A_43]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.83/1.56  tff(c_121, plain, (![A_71, B_72]: (r1_tarski(A_71, B_72) | ~m1_subset_1(A_71, k1_zfmisc_1(B_72)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.83/1.56  tff(c_129, plain, (![A_43]: (r1_tarski(k1_xboole_0, A_43))), inference(resolution, [status(thm)], [c_74, c_121])).
% 3.83/1.56  tff(c_98, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.83/1.56  tff(c_92, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.83/1.56  tff(c_96, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.83/1.56  tff(c_165, plain, (![A_83, B_84]: (k6_domain_1(A_83, B_84)=k1_tarski(B_84) | ~m1_subset_1(B_84, A_83) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.83/1.56  tff(c_174, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_96, c_165])).
% 3.83/1.56  tff(c_179, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_98, c_174])).
% 3.83/1.56  tff(c_94, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.83/1.56  tff(c_180, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_94])).
% 3.83/1.56  tff(c_244, plain, (![A_123, B_124]: (m1_subset_1(k6_domain_1(A_123, B_124), k1_zfmisc_1(A_123)) | ~m1_subset_1(B_124, A_123) | v1_xboole_0(A_123))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.83/1.56  tff(c_261, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_179, c_244])).
% 3.83/1.56  tff(c_269, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_261])).
% 3.83/1.56  tff(c_270, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_98, c_269])).
% 3.83/1.56  tff(c_941, plain, (![B_343, A_344]: (~v1_subset_1(B_343, A_344) | v1_xboole_0(B_343) | ~m1_subset_1(B_343, k1_zfmisc_1(A_344)) | ~v1_zfmisc_1(A_344) | v1_xboole_0(A_344))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.83/1.56  tff(c_950, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_270, c_941])).
% 3.83/1.56  tff(c_968, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_180, c_950])).
% 3.83/1.56  tff(c_969, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_98, c_968])).
% 3.83/1.56  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.83/1.56  tff(c_109, plain, (![B_64, A_65]: (~v1_xboole_0(B_64) | B_64=A_65 | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.83/1.56  tff(c_112, plain, (![A_65]: (k1_xboole_0=A_65 | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_2, c_109])).
% 3.83/1.56  tff(c_979, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_969, c_112])).
% 3.83/1.56  tff(c_6, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.83/1.56  tff(c_8, plain, (![A_4, B_5]: (k1_enumset1(A_4, A_4, B_5)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.83/1.56  tff(c_10, plain, (![A_6, B_7, C_8]: (k2_enumset1(A_6, A_6, B_7, C_8)=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.83/1.56  tff(c_12, plain, (![A_9, B_10, C_11, D_12]: (k3_enumset1(A_9, A_9, B_10, C_11, D_12)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.83/1.56  tff(c_14, plain, (![E_17, A_13, B_14, C_15, D_16]: (k4_enumset1(A_13, A_13, B_14, C_15, D_16, E_17)=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.83/1.56  tff(c_16, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (k5_enumset1(A_18, A_18, B_19, C_20, D_21, E_22, F_23)=k4_enumset1(A_18, B_19, C_20, D_21, E_22, F_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.83/1.56  tff(c_1082, plain, (![C_421, G_420, D_426, F_424, B_422, A_425, E_423]: (k6_enumset1(A_425, A_425, B_422, C_421, D_426, E_423, F_424, G_420)=k5_enumset1(A_425, B_422, C_421, D_426, E_423, F_424, G_420))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.83/1.56  tff(c_24, plain, (![A_31, C_33, B_32, H_38, F_36, E_35, D_34, J_42]: (r2_hidden(J_42, k6_enumset1(A_31, B_32, C_33, D_34, E_35, F_36, J_42, H_38)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.83/1.56  tff(c_1193, plain, (![E_430, F_434, D_432, C_428, A_429, B_433, G_431]: (r2_hidden(F_434, k5_enumset1(A_429, B_433, C_428, D_432, E_430, F_434, G_431)))), inference(superposition, [status(thm), theory('equality')], [c_1082, c_24])).
% 3.83/1.56  tff(c_1204, plain, (![D_439, B_440, C_436, F_438, E_437, A_435]: (r2_hidden(E_437, k4_enumset1(A_435, B_440, C_436, D_439, E_437, F_438)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1193])).
% 3.83/1.56  tff(c_1224, plain, (![C_446, A_445, E_444, B_443, D_442]: (r2_hidden(D_442, k3_enumset1(A_445, B_443, C_446, D_442, E_444)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1204])).
% 3.83/1.56  tff(c_1235, plain, (![C_447, A_448, B_449, D_450]: (r2_hidden(C_447, k2_enumset1(A_448, B_449, C_447, D_450)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1224])).
% 3.83/1.56  tff(c_1246, plain, (![B_451, A_452, C_453]: (r2_hidden(B_451, k1_enumset1(A_452, B_451, C_453)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1235])).
% 3.83/1.56  tff(c_1257, plain, (![A_454, B_455]: (r2_hidden(A_454, k2_tarski(A_454, B_455)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1246])).
% 3.83/1.56  tff(c_1268, plain, (![A_456]: (r2_hidden(A_456, k1_tarski(A_456)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1257])).
% 3.83/1.56  tff(c_1280, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_979, c_1268])).
% 3.83/1.56  tff(c_84, plain, (![B_53, A_52]: (~r1_tarski(B_53, A_52) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.83/1.56  tff(c_1335, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_1280, c_84])).
% 3.83/1.56  tff(c_1343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129, c_1335])).
% 3.83/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.56  
% 3.83/1.56  Inference rules
% 3.83/1.56  ----------------------
% 3.83/1.56  #Ref     : 0
% 3.83/1.56  #Sup     : 287
% 3.83/1.56  #Fact    : 0
% 3.83/1.56  #Define  : 0
% 3.83/1.56  #Split   : 2
% 3.83/1.56  #Chain   : 0
% 3.83/1.56  #Close   : 0
% 3.83/1.56  
% 3.83/1.56  Ordering : KBO
% 3.83/1.56  
% 3.83/1.56  Simplification rules
% 3.83/1.56  ----------------------
% 3.83/1.56  #Subsume      : 20
% 3.83/1.56  #Demod        : 89
% 3.83/1.56  #Tautology    : 98
% 3.83/1.56  #SimpNegUnit  : 21
% 3.83/1.56  #BackRed      : 19
% 3.83/1.56  
% 3.83/1.56  #Partial instantiations: 0
% 3.83/1.56  #Strategies tried      : 1
% 3.83/1.56  
% 3.83/1.56  Timing (in seconds)
% 3.83/1.56  ----------------------
% 3.83/1.57  Preprocessing        : 0.36
% 3.83/1.57  Parsing              : 0.17
% 3.83/1.57  CNF conversion       : 0.03
% 3.83/1.57  Main loop            : 0.46
% 3.83/1.57  Inferencing          : 0.15
% 3.83/1.57  Reduction            : 0.13
% 3.83/1.57  Demodulation         : 0.09
% 3.83/1.57  BG Simplification    : 0.03
% 3.83/1.57  Subsumption          : 0.11
% 3.83/1.57  Abstraction          : 0.03
% 3.83/1.57  MUC search           : 0.00
% 3.83/1.57  Cooper               : 0.00
% 3.83/1.57  Total                : 0.85
% 3.83/1.57  Index Insertion      : 0.00
% 3.83/1.57  Index Deletion       : 0.00
% 3.83/1.57  Index Matching       : 0.00
% 3.83/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
