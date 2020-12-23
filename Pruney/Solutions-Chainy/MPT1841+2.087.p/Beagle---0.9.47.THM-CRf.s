%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:39 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_131,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_103,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_74,plain,(
    ! [A_43] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_121,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(A_71,B_72)
      | ~ m1_subset_1(A_71,k1_zfmisc_1(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_129,plain,(
    ! [A_43] : r1_tarski(k1_xboole_0,A_43) ),
    inference(resolution,[status(thm)],[c_74,c_121])).

tff(c_98,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_92,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_96,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_164,plain,(
    ! [A_84,B_85] :
      ( k6_domain_1(A_84,B_85) = k1_tarski(B_85)
      | ~ m1_subset_1(B_85,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_173,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_164])).

tff(c_178,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_173])).

tff(c_94,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_179,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_94])).

tff(c_230,plain,(
    ! [A_112,B_113] :
      ( m1_subset_1(k6_domain_1(A_112,B_113),k1_zfmisc_1(A_112))
      | ~ m1_subset_1(B_113,A_112)
      | v1_xboole_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_247,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_230])).

tff(c_255,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_247])).

tff(c_256,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_255])).

tff(c_1143,plain,(
    ! [B_408,A_409] :
      ( ~ v1_subset_1(B_408,A_409)
      | v1_xboole_0(B_408)
      | ~ m1_subset_1(B_408,k1_zfmisc_1(A_409))
      | ~ v1_zfmisc_1(A_409)
      | v1_xboole_0(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1149,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_256,c_1143])).

tff(c_1162,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_179,c_1149])).

tff(c_1163,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_1162])).

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

tff(c_1173,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1163,c_112])).

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

tff(c_1344,plain,(
    ! [A_466,D_467,E_464,G_461,F_465,B_463,C_462] : k6_enumset1(A_466,A_466,B_463,C_462,D_467,E_464,F_465,G_461) = k5_enumset1(A_466,B_463,C_462,D_467,E_464,F_465,G_461) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    ! [C_33,B_32,H_38,F_36,E_35,G_37,D_34,J_42] : r2_hidden(J_42,k6_enumset1(J_42,B_32,C_33,D_34,E_35,F_36,G_37,H_38)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1401,plain,(
    ! [C_471,B_473,F_468,E_469,G_470,A_474,D_472] : r2_hidden(A_474,k5_enumset1(A_474,B_473,C_471,D_472,E_469,F_468,G_470)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1344,c_36])).

tff(c_1415,plain,(
    ! [C_476,B_480,F_478,E_477,A_475,D_479] : r2_hidden(A_475,k4_enumset1(A_475,B_480,C_476,D_479,E_477,F_478)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1401])).

tff(c_1429,plain,(
    ! [E_483,B_482,D_481,C_485,A_484] : r2_hidden(A_484,k3_enumset1(A_484,B_482,C_485,D_481,E_483)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1415])).

tff(c_1444,plain,(
    ! [A_486,B_487,C_488,D_489] : r2_hidden(A_486,k2_enumset1(A_486,B_487,C_488,D_489)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1429])).

tff(c_1458,plain,(
    ! [A_490,B_491,C_492] : r2_hidden(A_490,k1_enumset1(A_490,B_491,C_492)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1444])).

tff(c_1472,plain,(
    ! [A_493,B_494] : r2_hidden(A_493,k2_tarski(A_493,B_494)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1458])).

tff(c_1486,plain,(
    ! [A_495] : r2_hidden(A_495,k1_tarski(A_495)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1472])).

tff(c_1500,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1173,c_1486])).

tff(c_84,plain,(
    ! [B_53,A_52] :
      ( ~ r1_tarski(B_53,A_52)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1514,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_1500,c_84])).

tff(c_1525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_1514])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:02:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.58  
% 3.74/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.59  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.74/1.59  
% 3.74/1.59  %Foreground sorts:
% 3.74/1.59  
% 3.74/1.59  
% 3.74/1.59  %Background operators:
% 3.74/1.59  
% 3.74/1.59  
% 3.74/1.59  %Foreground operators:
% 3.74/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.74/1.59  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.74/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.74/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.74/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.74/1.59  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.74/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.74/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.74/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.74/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.74/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.74/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.74/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.74/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.74/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.74/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.59  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.74/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.74/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.74/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.74/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.74/1.59  
% 3.74/1.60  tff(f_80, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.74/1.60  tff(f_92, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.74/1.60  tff(f_143, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 3.74/1.60  tff(f_117, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.74/1.60  tff(f_110, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.74/1.60  tff(f_131, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.74/1.60  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.74/1.60  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.74/1.60  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.74/1.60  tff(f_38, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.74/1.60  tff(f_40, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.74/1.60  tff(f_42, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.74/1.60  tff(f_44, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.74/1.60  tff(f_46, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.74/1.60  tff(f_48, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.74/1.60  tff(f_78, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 3.74/1.60  tff(f_103, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.74/1.60  tff(c_74, plain, (![A_43]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.74/1.60  tff(c_121, plain, (![A_71, B_72]: (r1_tarski(A_71, B_72) | ~m1_subset_1(A_71, k1_zfmisc_1(B_72)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.74/1.60  tff(c_129, plain, (![A_43]: (r1_tarski(k1_xboole_0, A_43))), inference(resolution, [status(thm)], [c_74, c_121])).
% 3.74/1.60  tff(c_98, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.74/1.60  tff(c_92, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.74/1.60  tff(c_96, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.74/1.60  tff(c_164, plain, (![A_84, B_85]: (k6_domain_1(A_84, B_85)=k1_tarski(B_85) | ~m1_subset_1(B_85, A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.74/1.60  tff(c_173, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_96, c_164])).
% 3.74/1.60  tff(c_178, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_98, c_173])).
% 3.74/1.60  tff(c_94, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.74/1.60  tff(c_179, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_94])).
% 3.74/1.60  tff(c_230, plain, (![A_112, B_113]: (m1_subset_1(k6_domain_1(A_112, B_113), k1_zfmisc_1(A_112)) | ~m1_subset_1(B_113, A_112) | v1_xboole_0(A_112))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.74/1.60  tff(c_247, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_178, c_230])).
% 3.74/1.60  tff(c_255, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_247])).
% 3.74/1.60  tff(c_256, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_98, c_255])).
% 3.74/1.60  tff(c_1143, plain, (![B_408, A_409]: (~v1_subset_1(B_408, A_409) | v1_xboole_0(B_408) | ~m1_subset_1(B_408, k1_zfmisc_1(A_409)) | ~v1_zfmisc_1(A_409) | v1_xboole_0(A_409))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.74/1.60  tff(c_1149, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_256, c_1143])).
% 3.74/1.60  tff(c_1162, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_179, c_1149])).
% 3.74/1.60  tff(c_1163, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_98, c_1162])).
% 3.74/1.60  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.74/1.60  tff(c_109, plain, (![B_64, A_65]: (~v1_xboole_0(B_64) | B_64=A_65 | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.74/1.60  tff(c_112, plain, (![A_65]: (k1_xboole_0=A_65 | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_2, c_109])).
% 3.74/1.60  tff(c_1173, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1163, c_112])).
% 3.74/1.60  tff(c_6, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.74/1.60  tff(c_8, plain, (![A_4, B_5]: (k1_enumset1(A_4, A_4, B_5)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.74/1.60  tff(c_10, plain, (![A_6, B_7, C_8]: (k2_enumset1(A_6, A_6, B_7, C_8)=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.74/1.60  tff(c_12, plain, (![A_9, B_10, C_11, D_12]: (k3_enumset1(A_9, A_9, B_10, C_11, D_12)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.74/1.60  tff(c_14, plain, (![E_17, A_13, B_14, C_15, D_16]: (k4_enumset1(A_13, A_13, B_14, C_15, D_16, E_17)=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.74/1.60  tff(c_16, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (k5_enumset1(A_18, A_18, B_19, C_20, D_21, E_22, F_23)=k4_enumset1(A_18, B_19, C_20, D_21, E_22, F_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.74/1.60  tff(c_1344, plain, (![A_466, D_467, E_464, G_461, F_465, B_463, C_462]: (k6_enumset1(A_466, A_466, B_463, C_462, D_467, E_464, F_465, G_461)=k5_enumset1(A_466, B_463, C_462, D_467, E_464, F_465, G_461))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.74/1.60  tff(c_36, plain, (![C_33, B_32, H_38, F_36, E_35, G_37, D_34, J_42]: (r2_hidden(J_42, k6_enumset1(J_42, B_32, C_33, D_34, E_35, F_36, G_37, H_38)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.74/1.60  tff(c_1401, plain, (![C_471, B_473, F_468, E_469, G_470, A_474, D_472]: (r2_hidden(A_474, k5_enumset1(A_474, B_473, C_471, D_472, E_469, F_468, G_470)))), inference(superposition, [status(thm), theory('equality')], [c_1344, c_36])).
% 3.74/1.60  tff(c_1415, plain, (![C_476, B_480, F_478, E_477, A_475, D_479]: (r2_hidden(A_475, k4_enumset1(A_475, B_480, C_476, D_479, E_477, F_478)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1401])).
% 3.74/1.60  tff(c_1429, plain, (![E_483, B_482, D_481, C_485, A_484]: (r2_hidden(A_484, k3_enumset1(A_484, B_482, C_485, D_481, E_483)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1415])).
% 3.74/1.60  tff(c_1444, plain, (![A_486, B_487, C_488, D_489]: (r2_hidden(A_486, k2_enumset1(A_486, B_487, C_488, D_489)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1429])).
% 3.74/1.60  tff(c_1458, plain, (![A_490, B_491, C_492]: (r2_hidden(A_490, k1_enumset1(A_490, B_491, C_492)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1444])).
% 3.74/1.60  tff(c_1472, plain, (![A_493, B_494]: (r2_hidden(A_493, k2_tarski(A_493, B_494)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1458])).
% 3.74/1.60  tff(c_1486, plain, (![A_495]: (r2_hidden(A_495, k1_tarski(A_495)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1472])).
% 3.74/1.60  tff(c_1500, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1173, c_1486])).
% 3.74/1.60  tff(c_84, plain, (![B_53, A_52]: (~r1_tarski(B_53, A_52) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.74/1.60  tff(c_1514, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_1500, c_84])).
% 3.74/1.60  tff(c_1525, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129, c_1514])).
% 3.74/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.60  
% 3.74/1.60  Inference rules
% 3.74/1.60  ----------------------
% 3.74/1.60  #Ref     : 0
% 3.74/1.60  #Sup     : 334
% 3.74/1.60  #Fact    : 0
% 3.74/1.60  #Define  : 0
% 3.74/1.60  #Split   : 3
% 3.74/1.60  #Chain   : 0
% 3.74/1.60  #Close   : 0
% 3.74/1.60  
% 3.74/1.60  Ordering : KBO
% 3.74/1.60  
% 3.74/1.60  Simplification rules
% 3.74/1.60  ----------------------
% 3.74/1.60  #Subsume      : 25
% 3.74/1.60  #Demod        : 125
% 3.74/1.60  #Tautology    : 104
% 3.74/1.60  #SimpNegUnit  : 20
% 3.74/1.60  #BackRed      : 22
% 3.74/1.60  
% 3.74/1.60  #Partial instantiations: 0
% 3.74/1.60  #Strategies tried      : 1
% 3.74/1.60  
% 3.74/1.60  Timing (in seconds)
% 3.74/1.60  ----------------------
% 3.74/1.60  Preprocessing        : 0.36
% 3.74/1.60  Parsing              : 0.18
% 3.74/1.60  CNF conversion       : 0.03
% 3.74/1.60  Main loop            : 0.48
% 3.74/1.60  Inferencing          : 0.16
% 3.74/1.60  Reduction            : 0.14
% 3.74/1.60  Demodulation         : 0.09
% 3.74/1.60  BG Simplification    : 0.03
% 3.74/1.60  Subsumption          : 0.12
% 3.74/1.60  Abstraction          : 0.03
% 3.74/1.60  MUC search           : 0.00
% 3.74/1.60  Cooper               : 0.00
% 3.74/1.60  Total                : 0.88
% 3.74/1.60  Index Insertion      : 0.00
% 3.74/1.61  Index Deletion       : 0.00
% 3.74/1.61  Index Matching       : 0.00
% 3.74/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
