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
% DateTime   : Thu Dec  3 10:10:17 EST 2020

% Result     : Theorem 6.34s
% Output     : CNFRefutation 6.60s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 464 expanded)
%              Number of leaves         :   30 ( 199 expanded)
%              Depth                    :   20
%              Number of atoms          :  225 (3132 expanded)
%              Number of equality atoms :  167 (2019 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( m1_subset_1(F,k4_zfmisc_1(A,B,C,D))
       => ( ! [G] :
              ( m1_subset_1(G,A)
             => ! [H] :
                  ( m1_subset_1(H,B)
                 => ! [I] :
                      ( m1_subset_1(I,C)
                     => ! [J] :
                          ( m1_subset_1(J,D)
                         => ( F = k4_mcart_1(G,H,I,J)
                           => E = H ) ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k1_xboole_0
            | E = k9_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).

tff(f_114,axiom,(
    ! [A,B,C,D,E,F] :
      ( m1_subset_1(F,k4_zfmisc_1(A,B,C,D))
     => ( ! [G] :
            ( m1_subset_1(G,A)
           => ! [H] :
                ( m1_subset_1(H,B)
               => ! [I] :
                    ( m1_subset_1(I,C)
                   => ! [J] :
                        ( m1_subset_1(J,D)
                       => ( F = k4_mcart_1(G,H,I,J)
                         => E = G ) ) ) ) )
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | D = k1_xboole_0
          | E = k8_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_mcart_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ? [E] :
            ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
            & ? [F,G,H,I] :
                ( E = k4_mcart_1(F,G,H,I)
                & ~ ( k8_mcart_1(A,B,C,D,E) = F
                    & k9_mcart_1(A,B,C,D,E) = G
                    & k10_mcart_1(A,B,C,D,E) = H
                    & k11_mcart_1(A,B,C,D,E) = I ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_mcart_1)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_38,plain,(
    k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_50,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_30,plain,(
    ! [E_47,F_48,D_46,C_45,A_43,B_44] :
      ( m1_subset_1('#skF_4'(C_45,D_46,F_48,A_43,B_44,E_47),D_46)
      | k8_mcart_1(A_43,B_44,C_45,D_46,F_48) = E_47
      | k1_xboole_0 = D_46
      | k1_xboole_0 = C_45
      | k1_xboole_0 = B_44
      | k1_xboole_0 = A_43
      | ~ m1_subset_1(F_48,k4_zfmisc_1(A_43,B_44,C_45,D_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_32,plain,(
    ! [E_47,F_48,D_46,C_45,A_43,B_44] :
      ( m1_subset_1('#skF_3'(C_45,D_46,F_48,A_43,B_44,E_47),C_45)
      | k8_mcart_1(A_43,B_44,C_45,D_46,F_48) = E_47
      | k1_xboole_0 = D_46
      | k1_xboole_0 = C_45
      | k1_xboole_0 = B_44
      | k1_xboole_0 = A_43
      | ~ m1_subset_1(F_48,k4_zfmisc_1(A_43,B_44,C_45,D_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_36,plain,(
    ! [E_47,F_48,D_46,C_45,A_43,B_44] :
      ( m1_subset_1('#skF_1'(C_45,D_46,F_48,A_43,B_44,E_47),A_43)
      | k8_mcart_1(A_43,B_44,C_45,D_46,F_48) = E_47
      | k1_xboole_0 = D_46
      | k1_xboole_0 = C_45
      | k1_xboole_0 = B_44
      | k1_xboole_0 = A_43
      | ~ m1_subset_1(F_48,k4_zfmisc_1(A_43,B_44,C_45,D_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_34,plain,(
    ! [E_47,F_48,D_46,C_45,A_43,B_44] :
      ( m1_subset_1('#skF_2'(C_45,D_46,F_48,A_43,B_44,E_47),B_44)
      | k8_mcart_1(A_43,B_44,C_45,D_46,F_48) = E_47
      | k1_xboole_0 = D_46
      | k1_xboole_0 = C_45
      | k1_xboole_0 = B_44
      | k1_xboole_0 = A_43
      | ~ m1_subset_1(F_48,k4_zfmisc_1(A_43,B_44,C_45,D_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_621,plain,(
    ! [E_285,F_282,A_283,D_281,C_280,B_284] :
      ( k4_mcart_1('#skF_1'(C_280,D_281,F_282,A_283,B_284,E_285),'#skF_2'(C_280,D_281,F_282,A_283,B_284,E_285),'#skF_3'(C_280,D_281,F_282,A_283,B_284,E_285),'#skF_4'(C_280,D_281,F_282,A_283,B_284,E_285)) = F_282
      | k8_mcart_1(A_283,B_284,C_280,D_281,F_282) = E_285
      | k1_xboole_0 = D_281
      | k1_xboole_0 = C_280
      | k1_xboole_0 = B_284
      | k1_xboole_0 = A_283
      | ~ m1_subset_1(F_282,k4_zfmisc_1(A_283,B_284,C_280,D_281)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_48,plain,(
    ! [H_98,G_90,I_102,J_104] :
      ( H_98 = '#skF_9'
      | k4_mcart_1(G_90,H_98,I_102,J_104) != '#skF_10'
      | ~ m1_subset_1(J_104,'#skF_8')
      | ~ m1_subset_1(I_102,'#skF_7')
      | ~ m1_subset_1(H_98,'#skF_6')
      | ~ m1_subset_1(G_90,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_727,plain,(
    ! [C_312,F_314,B_311,D_309,E_310,A_313] :
      ( '#skF_2'(C_312,D_309,F_314,A_313,B_311,E_310) = '#skF_9'
      | F_314 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_312,D_309,F_314,A_313,B_311,E_310),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_312,D_309,F_314,A_313,B_311,E_310),'#skF_7')
      | ~ m1_subset_1('#skF_2'(C_312,D_309,F_314,A_313,B_311,E_310),'#skF_6')
      | ~ m1_subset_1('#skF_1'(C_312,D_309,F_314,A_313,B_311,E_310),'#skF_5')
      | k8_mcart_1(A_313,B_311,C_312,D_309,F_314) = E_310
      | k1_xboole_0 = D_309
      | k1_xboole_0 = C_312
      | k1_xboole_0 = B_311
      | k1_xboole_0 = A_313
      | ~ m1_subset_1(F_314,k4_zfmisc_1(A_313,B_311,C_312,D_309)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_48])).

tff(c_731,plain,(
    ! [E_47,F_48,D_46,C_45,A_43] :
      ( '#skF_2'(C_45,D_46,F_48,A_43,'#skF_6',E_47) = '#skF_9'
      | F_48 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_45,D_46,F_48,A_43,'#skF_6',E_47),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_45,D_46,F_48,A_43,'#skF_6',E_47),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_45,D_46,F_48,A_43,'#skF_6',E_47),'#skF_5')
      | k8_mcart_1(A_43,'#skF_6',C_45,D_46,F_48) = E_47
      | k1_xboole_0 = D_46
      | k1_xboole_0 = C_45
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_43
      | ~ m1_subset_1(F_48,k4_zfmisc_1(A_43,'#skF_6',C_45,D_46)) ) ),
    inference(resolution,[status(thm)],[c_34,c_727])).

tff(c_814,plain,(
    ! [C_338,E_342,A_341,D_339,F_340] :
      ( '#skF_2'(C_338,D_339,F_340,A_341,'#skF_6',E_342) = '#skF_9'
      | F_340 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_338,D_339,F_340,A_341,'#skF_6',E_342),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_338,D_339,F_340,A_341,'#skF_6',E_342),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_338,D_339,F_340,A_341,'#skF_6',E_342),'#skF_5')
      | k8_mcart_1(A_341,'#skF_6',C_338,D_339,F_340) = E_342
      | k1_xboole_0 = D_339
      | k1_xboole_0 = C_338
      | k1_xboole_0 = A_341
      | ~ m1_subset_1(F_340,k4_zfmisc_1(A_341,'#skF_6',C_338,D_339)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_731])).

tff(c_818,plain,(
    ! [C_45,D_46,F_48,E_47] :
      ( '#skF_2'(C_45,D_46,F_48,'#skF_5','#skF_6',E_47) = '#skF_9'
      | F_48 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_45,D_46,F_48,'#skF_5','#skF_6',E_47),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_45,D_46,F_48,'#skF_5','#skF_6',E_47),'#skF_7')
      | k8_mcart_1('#skF_5','#skF_6',C_45,D_46,F_48) = E_47
      | k1_xboole_0 = D_46
      | k1_xboole_0 = C_45
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_48,k4_zfmisc_1('#skF_5','#skF_6',C_45,D_46)) ) ),
    inference(resolution,[status(thm)],[c_36,c_814])).

tff(c_964,plain,(
    ! [C_408,D_409,F_410,E_411] :
      ( '#skF_2'(C_408,D_409,F_410,'#skF_5','#skF_6',E_411) = '#skF_9'
      | F_410 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_408,D_409,F_410,'#skF_5','#skF_6',E_411),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_408,D_409,F_410,'#skF_5','#skF_6',E_411),'#skF_7')
      | k8_mcart_1('#skF_5','#skF_6',C_408,D_409,F_410) = E_411
      | k1_xboole_0 = D_409
      | k1_xboole_0 = C_408
      | ~ m1_subset_1(F_410,k4_zfmisc_1('#skF_5','#skF_6',C_408,D_409)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_46,c_818])).

tff(c_968,plain,(
    ! [D_46,F_48,E_47] :
      ( '#skF_2'('#skF_7',D_46,F_48,'#skF_5','#skF_6',E_47) = '#skF_9'
      | F_48 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_7',D_46,F_48,'#skF_5','#skF_6',E_47),'#skF_8')
      | k8_mcart_1('#skF_5','#skF_6','#skF_7',D_46,F_48) = E_47
      | k1_xboole_0 = D_46
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_48,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_46)) ) ),
    inference(resolution,[status(thm)],[c_32,c_964])).

tff(c_973,plain,(
    ! [D_412,F_413,E_414] :
      ( '#skF_2'('#skF_7',D_412,F_413,'#skF_5','#skF_6',E_414) = '#skF_9'
      | F_413 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_7',D_412,F_413,'#skF_5','#skF_6',E_414),'#skF_8')
      | k8_mcart_1('#skF_5','#skF_6','#skF_7',D_412,F_413) = E_414
      | k1_xboole_0 = D_412
      | ~ m1_subset_1(F_413,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_412)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_42,c_42,c_968])).

tff(c_977,plain,(
    ! [F_48,E_47] :
      ( '#skF_2'('#skF_7','#skF_8',F_48,'#skF_5','#skF_6',E_47) = '#skF_9'
      | F_48 != '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_48) = E_47
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_48,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_30,c_973])).

tff(c_982,plain,(
    ! [F_415,E_416] :
      ( '#skF_2'('#skF_7','#skF_8',F_415,'#skF_5','#skF_6',E_416) = '#skF_9'
      | F_415 != '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_415) = E_416
      | ~ m1_subset_1(F_415,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_42,c_40,c_40,c_977])).

tff(c_1004,plain,(
    ! [E_417] :
      ( '#skF_2'('#skF_7','#skF_8','#skF_10','#skF_5','#skF_6',E_417) = '#skF_9'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_417 ) ),
    inference(resolution,[status(thm)],[c_50,c_982])).

tff(c_28,plain,(
    ! [E_47,F_48,D_46,C_45,A_43,B_44] :
      ( k4_mcart_1('#skF_1'(C_45,D_46,F_48,A_43,B_44,E_47),'#skF_2'(C_45,D_46,F_48,A_43,B_44,E_47),'#skF_3'(C_45,D_46,F_48,A_43,B_44,E_47),'#skF_4'(C_45,D_46,F_48,A_43,B_44,E_47)) = F_48
      | k8_mcart_1(A_43,B_44,C_45,D_46,F_48) = E_47
      | k1_xboole_0 = D_46
      | k1_xboole_0 = C_45
      | k1_xboole_0 = B_44
      | k1_xboole_0 = A_43
      | ~ m1_subset_1(F_48,k4_zfmisc_1(A_43,B_44,C_45,D_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1013,plain,(
    ! [E_417] :
      ( k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_10','#skF_5','#skF_6',E_417),'#skF_9','#skF_3'('#skF_7','#skF_8','#skF_10','#skF_5','#skF_6',E_417),'#skF_4'('#skF_7','#skF_8','#skF_10','#skF_5','#skF_6',E_417)) = '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_417
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_417 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1004,c_28])).

tff(c_1599,plain,(
    ! [E_417] :
      ( k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_10','#skF_5','#skF_6',E_417),'#skF_9','#skF_3'('#skF_7','#skF_8','#skF_10','#skF_5','#skF_6',E_417),'#skF_4'('#skF_7','#skF_8','#skF_10','#skF_5','#skF_6',E_417)) = '#skF_10'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_417 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1013])).

tff(c_1600,plain,(
    ! [E_417] :
      ( k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_10','#skF_5','#skF_6',E_417),'#skF_9','#skF_3'('#skF_7','#skF_8','#skF_10','#skF_5','#skF_6',E_417),'#skF_4'('#skF_7','#skF_8','#skF_10','#skF_5','#skF_6',E_417)) = '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_417 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_42,c_40,c_1599])).

tff(c_1687,plain,(
    ! [E_4726] :
      ( k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_10','#skF_5','#skF_6',E_4726),'#skF_9','#skF_3'('#skF_7','#skF_8','#skF_10','#skF_5','#skF_6',E_4726),'#skF_4'('#skF_7','#skF_8','#skF_10','#skF_5','#skF_6',E_4726)) = '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_4726 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_42,c_40,c_1599])).

tff(c_14,plain,(
    ! [B_16,A_15,D_18,H_35,G_34,F_33,C_17,I_36] :
      ( k9_mcart_1(A_15,B_16,C_17,D_18,k4_mcart_1(F_33,G_34,H_35,I_36)) = G_34
      | ~ m1_subset_1(k4_mcart_1(F_33,G_34,H_35,I_36),k4_zfmisc_1(A_15,B_16,C_17,D_18))
      | k1_xboole_0 = D_18
      | k1_xboole_0 = C_17
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2517,plain,(
    ! [E_6327,D_6325,C_6324,B_6326,A_6328] :
      ( k9_mcart_1(A_6328,B_6326,C_6324,D_6325,k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_10','#skF_5','#skF_6',E_6327),'#skF_9','#skF_3'('#skF_7','#skF_8','#skF_10','#skF_5','#skF_6',E_6327),'#skF_4'('#skF_7','#skF_8','#skF_10','#skF_5','#skF_6',E_6327))) = '#skF_9'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_6328,B_6326,C_6324,D_6325))
      | k1_xboole_0 = D_6325
      | k1_xboole_0 = C_6324
      | k1_xboole_0 = B_6326
      | k1_xboole_0 = A_6328
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_6327 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1687,c_14])).

tff(c_2526,plain,(
    ! [D_6325,C_6324,B_6326,E_417,A_6328] :
      ( k9_mcart_1(A_6328,B_6326,C_6324,D_6325,'#skF_10') = '#skF_9'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_6328,B_6326,C_6324,D_6325))
      | k1_xboole_0 = D_6325
      | k1_xboole_0 = C_6324
      | k1_xboole_0 = B_6326
      | k1_xboole_0 = A_6328
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_417
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_417 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1600,c_2517])).

tff(c_2556,plain,(
    ! [E_417] :
      ( k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_417
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_417 ) ),
    inference(splitLeft,[status(thm)],[c_2526])).

tff(c_4624,plain,(
    k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_7' ),
    inference(factorization,[status(thm),theory(equality)],[c_2556])).

tff(c_2577,plain,(
    ! [E_417] : k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_417 ),
    inference(factorization,[status(thm),theory(equality)],[c_2556])).

tff(c_5691,plain,(
    ! [E_23675] : E_23675 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_4624,c_2577])).

tff(c_6264,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5691,c_42])).

tff(c_6266,plain,(
    ! [A_29372,B_29373,C_29374,D_29375] :
      ( k9_mcart_1(A_29372,B_29373,C_29374,D_29375,'#skF_10') = '#skF_9'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_29372,B_29373,C_29374,D_29375))
      | k1_xboole_0 = D_29375
      | k1_xboole_0 = C_29374
      | k1_xboole_0 = B_29373
      | k1_xboole_0 = A_29372 ) ),
    inference(splitRight,[status(thm)],[c_2526])).

tff(c_6276,plain,
    ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_6266])).

tff(c_6280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_42,c_40,c_38,c_6276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:48:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.34/2.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/2.34  
% 6.34/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/2.34  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4
% 6.34/2.34  
% 6.34/2.34  %Foreground sorts:
% 6.34/2.34  
% 6.34/2.34  
% 6.34/2.34  %Background operators:
% 6.34/2.34  
% 6.34/2.34  
% 6.34/2.34  %Foreground operators:
% 6.34/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.34/2.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 6.34/2.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 6.34/2.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.34/2.34  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 6.34/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.34/2.34  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 6.34/2.34  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 6.34/2.34  tff('#skF_7', type, '#skF_7': $i).
% 6.34/2.34  tff('#skF_10', type, '#skF_10': $i).
% 6.34/2.34  tff('#skF_5', type, '#skF_5': $i).
% 6.34/2.34  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 6.34/2.34  tff('#skF_6', type, '#skF_6': $i).
% 6.34/2.34  tff('#skF_9', type, '#skF_9': $i).
% 6.34/2.34  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 6.34/2.34  tff('#skF_8', type, '#skF_8': $i).
% 6.34/2.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 6.34/2.34  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 6.34/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.34/2.34  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 6.34/2.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.34/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.34/2.34  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 6.34/2.34  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 6.34/2.34  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 6.34/2.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 6.34/2.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.34/2.34  
% 6.60/2.36  tff(f_143, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = H)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k9_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_mcart_1)).
% 6.60/2.36  tff(f_114, axiom, (![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = G)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k8_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_mcart_1)).
% 6.60/2.36  tff(f_61, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_mcart_1)).
% 6.60/2.36  tff(c_46, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.60/2.36  tff(c_44, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.60/2.36  tff(c_42, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.60/2.36  tff(c_40, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.60/2.36  tff(c_38, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.60/2.36  tff(c_50, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.60/2.36  tff(c_30, plain, (![E_47, F_48, D_46, C_45, A_43, B_44]: (m1_subset_1('#skF_4'(C_45, D_46, F_48, A_43, B_44, E_47), D_46) | k8_mcart_1(A_43, B_44, C_45, D_46, F_48)=E_47 | k1_xboole_0=D_46 | k1_xboole_0=C_45 | k1_xboole_0=B_44 | k1_xboole_0=A_43 | ~m1_subset_1(F_48, k4_zfmisc_1(A_43, B_44, C_45, D_46)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.60/2.36  tff(c_32, plain, (![E_47, F_48, D_46, C_45, A_43, B_44]: (m1_subset_1('#skF_3'(C_45, D_46, F_48, A_43, B_44, E_47), C_45) | k8_mcart_1(A_43, B_44, C_45, D_46, F_48)=E_47 | k1_xboole_0=D_46 | k1_xboole_0=C_45 | k1_xboole_0=B_44 | k1_xboole_0=A_43 | ~m1_subset_1(F_48, k4_zfmisc_1(A_43, B_44, C_45, D_46)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.60/2.36  tff(c_36, plain, (![E_47, F_48, D_46, C_45, A_43, B_44]: (m1_subset_1('#skF_1'(C_45, D_46, F_48, A_43, B_44, E_47), A_43) | k8_mcart_1(A_43, B_44, C_45, D_46, F_48)=E_47 | k1_xboole_0=D_46 | k1_xboole_0=C_45 | k1_xboole_0=B_44 | k1_xboole_0=A_43 | ~m1_subset_1(F_48, k4_zfmisc_1(A_43, B_44, C_45, D_46)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.60/2.36  tff(c_34, plain, (![E_47, F_48, D_46, C_45, A_43, B_44]: (m1_subset_1('#skF_2'(C_45, D_46, F_48, A_43, B_44, E_47), B_44) | k8_mcart_1(A_43, B_44, C_45, D_46, F_48)=E_47 | k1_xboole_0=D_46 | k1_xboole_0=C_45 | k1_xboole_0=B_44 | k1_xboole_0=A_43 | ~m1_subset_1(F_48, k4_zfmisc_1(A_43, B_44, C_45, D_46)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.60/2.36  tff(c_621, plain, (![E_285, F_282, A_283, D_281, C_280, B_284]: (k4_mcart_1('#skF_1'(C_280, D_281, F_282, A_283, B_284, E_285), '#skF_2'(C_280, D_281, F_282, A_283, B_284, E_285), '#skF_3'(C_280, D_281, F_282, A_283, B_284, E_285), '#skF_4'(C_280, D_281, F_282, A_283, B_284, E_285))=F_282 | k8_mcart_1(A_283, B_284, C_280, D_281, F_282)=E_285 | k1_xboole_0=D_281 | k1_xboole_0=C_280 | k1_xboole_0=B_284 | k1_xboole_0=A_283 | ~m1_subset_1(F_282, k4_zfmisc_1(A_283, B_284, C_280, D_281)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.60/2.36  tff(c_48, plain, (![H_98, G_90, I_102, J_104]: (H_98='#skF_9' | k4_mcart_1(G_90, H_98, I_102, J_104)!='#skF_10' | ~m1_subset_1(J_104, '#skF_8') | ~m1_subset_1(I_102, '#skF_7') | ~m1_subset_1(H_98, '#skF_6') | ~m1_subset_1(G_90, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.60/2.36  tff(c_727, plain, (![C_312, F_314, B_311, D_309, E_310, A_313]: ('#skF_2'(C_312, D_309, F_314, A_313, B_311, E_310)='#skF_9' | F_314!='#skF_10' | ~m1_subset_1('#skF_4'(C_312, D_309, F_314, A_313, B_311, E_310), '#skF_8') | ~m1_subset_1('#skF_3'(C_312, D_309, F_314, A_313, B_311, E_310), '#skF_7') | ~m1_subset_1('#skF_2'(C_312, D_309, F_314, A_313, B_311, E_310), '#skF_6') | ~m1_subset_1('#skF_1'(C_312, D_309, F_314, A_313, B_311, E_310), '#skF_5') | k8_mcart_1(A_313, B_311, C_312, D_309, F_314)=E_310 | k1_xboole_0=D_309 | k1_xboole_0=C_312 | k1_xboole_0=B_311 | k1_xboole_0=A_313 | ~m1_subset_1(F_314, k4_zfmisc_1(A_313, B_311, C_312, D_309)))), inference(superposition, [status(thm), theory('equality')], [c_621, c_48])).
% 6.60/2.36  tff(c_731, plain, (![E_47, F_48, D_46, C_45, A_43]: ('#skF_2'(C_45, D_46, F_48, A_43, '#skF_6', E_47)='#skF_9' | F_48!='#skF_10' | ~m1_subset_1('#skF_4'(C_45, D_46, F_48, A_43, '#skF_6', E_47), '#skF_8') | ~m1_subset_1('#skF_3'(C_45, D_46, F_48, A_43, '#skF_6', E_47), '#skF_7') | ~m1_subset_1('#skF_1'(C_45, D_46, F_48, A_43, '#skF_6', E_47), '#skF_5') | k8_mcart_1(A_43, '#skF_6', C_45, D_46, F_48)=E_47 | k1_xboole_0=D_46 | k1_xboole_0=C_45 | k1_xboole_0='#skF_6' | k1_xboole_0=A_43 | ~m1_subset_1(F_48, k4_zfmisc_1(A_43, '#skF_6', C_45, D_46)))), inference(resolution, [status(thm)], [c_34, c_727])).
% 6.60/2.36  tff(c_814, plain, (![C_338, E_342, A_341, D_339, F_340]: ('#skF_2'(C_338, D_339, F_340, A_341, '#skF_6', E_342)='#skF_9' | F_340!='#skF_10' | ~m1_subset_1('#skF_4'(C_338, D_339, F_340, A_341, '#skF_6', E_342), '#skF_8') | ~m1_subset_1('#skF_3'(C_338, D_339, F_340, A_341, '#skF_6', E_342), '#skF_7') | ~m1_subset_1('#skF_1'(C_338, D_339, F_340, A_341, '#skF_6', E_342), '#skF_5') | k8_mcart_1(A_341, '#skF_6', C_338, D_339, F_340)=E_342 | k1_xboole_0=D_339 | k1_xboole_0=C_338 | k1_xboole_0=A_341 | ~m1_subset_1(F_340, k4_zfmisc_1(A_341, '#skF_6', C_338, D_339)))), inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_731])).
% 6.60/2.36  tff(c_818, plain, (![C_45, D_46, F_48, E_47]: ('#skF_2'(C_45, D_46, F_48, '#skF_5', '#skF_6', E_47)='#skF_9' | F_48!='#skF_10' | ~m1_subset_1('#skF_4'(C_45, D_46, F_48, '#skF_5', '#skF_6', E_47), '#skF_8') | ~m1_subset_1('#skF_3'(C_45, D_46, F_48, '#skF_5', '#skF_6', E_47), '#skF_7') | k8_mcart_1('#skF_5', '#skF_6', C_45, D_46, F_48)=E_47 | k1_xboole_0=D_46 | k1_xboole_0=C_45 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_48, k4_zfmisc_1('#skF_5', '#skF_6', C_45, D_46)))), inference(resolution, [status(thm)], [c_36, c_814])).
% 6.60/2.36  tff(c_964, plain, (![C_408, D_409, F_410, E_411]: ('#skF_2'(C_408, D_409, F_410, '#skF_5', '#skF_6', E_411)='#skF_9' | F_410!='#skF_10' | ~m1_subset_1('#skF_4'(C_408, D_409, F_410, '#skF_5', '#skF_6', E_411), '#skF_8') | ~m1_subset_1('#skF_3'(C_408, D_409, F_410, '#skF_5', '#skF_6', E_411), '#skF_7') | k8_mcart_1('#skF_5', '#skF_6', C_408, D_409, F_410)=E_411 | k1_xboole_0=D_409 | k1_xboole_0=C_408 | ~m1_subset_1(F_410, k4_zfmisc_1('#skF_5', '#skF_6', C_408, D_409)))), inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_46, c_818])).
% 6.60/2.36  tff(c_968, plain, (![D_46, F_48, E_47]: ('#skF_2'('#skF_7', D_46, F_48, '#skF_5', '#skF_6', E_47)='#skF_9' | F_48!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_7', D_46, F_48, '#skF_5', '#skF_6', E_47), '#skF_8') | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', D_46, F_48)=E_47 | k1_xboole_0=D_46 | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_48, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_46)))), inference(resolution, [status(thm)], [c_32, c_964])).
% 6.60/2.36  tff(c_973, plain, (![D_412, F_413, E_414]: ('#skF_2'('#skF_7', D_412, F_413, '#skF_5', '#skF_6', E_414)='#skF_9' | F_413!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_7', D_412, F_413, '#skF_5', '#skF_6', E_414), '#skF_8') | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', D_412, F_413)=E_414 | k1_xboole_0=D_412 | ~m1_subset_1(F_413, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_412)))), inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_42, c_42, c_968])).
% 6.60/2.36  tff(c_977, plain, (![F_48, E_47]: ('#skF_2'('#skF_7', '#skF_8', F_48, '#skF_5', '#skF_6', E_47)='#skF_9' | F_48!='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_48)=E_47 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_48, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_30, c_973])).
% 6.60/2.36  tff(c_982, plain, (![F_415, E_416]: ('#skF_2'('#skF_7', '#skF_8', F_415, '#skF_5', '#skF_6', E_416)='#skF_9' | F_415!='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_415)=E_416 | ~m1_subset_1(F_415, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_42, c_40, c_40, c_977])).
% 6.60/2.36  tff(c_1004, plain, (![E_417]: ('#skF_2'('#skF_7', '#skF_8', '#skF_10', '#skF_5', '#skF_6', E_417)='#skF_9' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_417)), inference(resolution, [status(thm)], [c_50, c_982])).
% 6.60/2.36  tff(c_28, plain, (![E_47, F_48, D_46, C_45, A_43, B_44]: (k4_mcart_1('#skF_1'(C_45, D_46, F_48, A_43, B_44, E_47), '#skF_2'(C_45, D_46, F_48, A_43, B_44, E_47), '#skF_3'(C_45, D_46, F_48, A_43, B_44, E_47), '#skF_4'(C_45, D_46, F_48, A_43, B_44, E_47))=F_48 | k8_mcart_1(A_43, B_44, C_45, D_46, F_48)=E_47 | k1_xboole_0=D_46 | k1_xboole_0=C_45 | k1_xboole_0=B_44 | k1_xboole_0=A_43 | ~m1_subset_1(F_48, k4_zfmisc_1(A_43, B_44, C_45, D_46)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.60/2.36  tff(c_1013, plain, (![E_417]: (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_10', '#skF_5', '#skF_6', E_417), '#skF_9', '#skF_3'('#skF_7', '#skF_8', '#skF_10', '#skF_5', '#skF_6', E_417), '#skF_4'('#skF_7', '#skF_8', '#skF_10', '#skF_5', '#skF_6', E_417))='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_417 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_417)), inference(superposition, [status(thm), theory('equality')], [c_1004, c_28])).
% 6.60/2.36  tff(c_1599, plain, (![E_417]: (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_10', '#skF_5', '#skF_6', E_417), '#skF_9', '#skF_3'('#skF_7', '#skF_8', '#skF_10', '#skF_5', '#skF_6', E_417), '#skF_4'('#skF_7', '#skF_8', '#skF_10', '#skF_5', '#skF_6', E_417))='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_417)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1013])).
% 6.60/2.36  tff(c_1600, plain, (![E_417]: (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_10', '#skF_5', '#skF_6', E_417), '#skF_9', '#skF_3'('#skF_7', '#skF_8', '#skF_10', '#skF_5', '#skF_6', E_417), '#skF_4'('#skF_7', '#skF_8', '#skF_10', '#skF_5', '#skF_6', E_417))='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_417)), inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_42, c_40, c_1599])).
% 6.60/2.36  tff(c_1687, plain, (![E_4726]: (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_10', '#skF_5', '#skF_6', E_4726), '#skF_9', '#skF_3'('#skF_7', '#skF_8', '#skF_10', '#skF_5', '#skF_6', E_4726), '#skF_4'('#skF_7', '#skF_8', '#skF_10', '#skF_5', '#skF_6', E_4726))='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_4726)), inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_42, c_40, c_1599])).
% 6.60/2.36  tff(c_14, plain, (![B_16, A_15, D_18, H_35, G_34, F_33, C_17, I_36]: (k9_mcart_1(A_15, B_16, C_17, D_18, k4_mcart_1(F_33, G_34, H_35, I_36))=G_34 | ~m1_subset_1(k4_mcart_1(F_33, G_34, H_35, I_36), k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.60/2.36  tff(c_2517, plain, (![E_6327, D_6325, C_6324, B_6326, A_6328]: (k9_mcart_1(A_6328, B_6326, C_6324, D_6325, k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_10', '#skF_5', '#skF_6', E_6327), '#skF_9', '#skF_3'('#skF_7', '#skF_8', '#skF_10', '#skF_5', '#skF_6', E_6327), '#skF_4'('#skF_7', '#skF_8', '#skF_10', '#skF_5', '#skF_6', E_6327)))='#skF_9' | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_6328, B_6326, C_6324, D_6325)) | k1_xboole_0=D_6325 | k1_xboole_0=C_6324 | k1_xboole_0=B_6326 | k1_xboole_0=A_6328 | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_6327)), inference(superposition, [status(thm), theory('equality')], [c_1687, c_14])).
% 6.60/2.36  tff(c_2526, plain, (![D_6325, C_6324, B_6326, E_417, A_6328]: (k9_mcart_1(A_6328, B_6326, C_6324, D_6325, '#skF_10')='#skF_9' | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_6328, B_6326, C_6324, D_6325)) | k1_xboole_0=D_6325 | k1_xboole_0=C_6324 | k1_xboole_0=B_6326 | k1_xboole_0=A_6328 | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_417 | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_417)), inference(superposition, [status(thm), theory('equality')], [c_1600, c_2517])).
% 6.60/2.36  tff(c_2556, plain, (![E_417]: (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_417 | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_417)), inference(splitLeft, [status(thm)], [c_2526])).
% 6.60/2.36  tff(c_4624, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_7'), inference(factorization, [status(thm), theory('equality')], [c_2556])).
% 6.60/2.36  tff(c_2577, plain, (![E_417]: (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_417)), inference(factorization, [status(thm), theory('equality')], [c_2556])).
% 6.60/2.36  tff(c_5691, plain, (![E_23675]: (E_23675='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4624, c_2577])).
% 6.60/2.36  tff(c_6264, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5691, c_42])).
% 6.60/2.36  tff(c_6266, plain, (![A_29372, B_29373, C_29374, D_29375]: (k9_mcart_1(A_29372, B_29373, C_29374, D_29375, '#skF_10')='#skF_9' | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_29372, B_29373, C_29374, D_29375)) | k1_xboole_0=D_29375 | k1_xboole_0=C_29374 | k1_xboole_0=B_29373 | k1_xboole_0=A_29372)), inference(splitRight, [status(thm)], [c_2526])).
% 6.60/2.36  tff(c_6276, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_6266])).
% 6.60/2.36  tff(c_6280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_42, c_40, c_38, c_6276])).
% 6.60/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.60/2.36  
% 6.60/2.36  Inference rules
% 6.60/2.36  ----------------------
% 6.60/2.36  #Ref     : 0
% 6.60/2.36  #Sup     : 826
% 6.60/2.36  #Fact    : 4
% 6.60/2.36  #Define  : 0
% 6.60/2.36  #Split   : 10
% 6.60/2.36  #Chain   : 0
% 6.60/2.36  #Close   : 0
% 6.60/2.36  
% 6.60/2.36  Ordering : KBO
% 6.60/2.36  
% 6.60/2.36  Simplification rules
% 6.60/2.36  ----------------------
% 6.60/2.36  #Subsume      : 105
% 6.60/2.36  #Demod        : 355
% 6.60/2.36  #Tautology    : 124
% 6.60/2.36  #SimpNegUnit  : 37
% 6.60/2.36  #BackRed      : 0
% 6.60/2.36  
% 6.60/2.36  #Partial instantiations: 8404
% 6.60/2.36  #Strategies tried      : 1
% 6.60/2.36  
% 6.60/2.36  Timing (in seconds)
% 6.60/2.36  ----------------------
% 6.63/2.37  Preprocessing        : 0.37
% 6.63/2.37  Parsing              : 0.19
% 6.63/2.37  CNF conversion       : 0.03
% 6.63/2.37  Main loop            : 1.17
% 6.63/2.37  Inferencing          : 0.56
% 6.63/2.37  Reduction            : 0.31
% 6.63/2.37  Demodulation         : 0.22
% 6.63/2.37  BG Simplification    : 0.07
% 6.63/2.37  Subsumption          : 0.17
% 6.63/2.37  Abstraction          : 0.09
% 6.63/2.37  MUC search           : 0.00
% 6.63/2.37  Cooper               : 0.00
% 6.63/2.37  Total                : 1.58
% 6.63/2.37  Index Insertion      : 0.00
% 6.63/2.37  Index Deletion       : 0.00
% 6.63/2.37  Index Matching       : 0.00
% 6.63/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
