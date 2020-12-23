%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:15 EST 2020

% Result     : Theorem 6.15s
% Output     : CNFRefutation 6.26s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 435 expanded)
%              Number of leaves         :   39 ( 177 expanded)
%              Depth                    :   12
%              Number of atoms          :  558 (2482 expanded)
%              Number of equality atoms :   90 ( 446 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k2_enumset1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_tmap_1,type,(
    k1_tmap_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_201,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( ~ v1_xboole_0(C)
                  & m1_subset_1(C,k1_zfmisc_1(A)) )
               => ! [D] :
                    ( ( ~ v1_xboole_0(D)
                      & m1_subset_1(D,k1_zfmisc_1(A)) )
                   => ( r1_subset_1(C,D)
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,C,B)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,D,B)
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                             => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                                & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),C) = E
                                & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),D) = F ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_159,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & ~ v1_xboole_0(C)
        & m1_subset_1(C,k1_zfmisc_1(A))
        & ~ v1_xboole_0(D)
        & m1_subset_1(D,k1_zfmisc_1(A))
        & v1_funct_1(E)
        & v1_funct_2(E,C,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,D,B)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
     => ( v1_funct_1(k1_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k1_tmap_1(A,B,C,D,E,F),k4_subset_1(A,C,D),B)
        & m1_subset_1(k1_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_125,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & m1_subset_1(C,k1_zfmisc_1(A)) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,C,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,D,B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                         => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,k4_subset_1(A,C,D),B)
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) )
                               => ( G = k1_tmap_1(A,B,C,D,E,F)
                                <=> ( k2_partfun1(k4_subset_1(A,C,D),B,G,C) = E
                                    & k2_partfun1(k4_subset_1(A,C,D),B,G,D) = F ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_358,plain,(
    ! [C_259,A_260,B_261] :
      ( v1_relat_1(C_259)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_366,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_358])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_389,plain,(
    ! [A_266,B_267] :
      ( v1_xboole_0(k7_relat_1(A_266,B_267))
      | ~ v1_xboole_0(B_267)
      | ~ v1_relat_1(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_394,plain,(
    ! [A_268,B_269] :
      ( k7_relat_1(A_268,B_269) = k1_xboole_0
      | ~ v1_xboole_0(B_269)
      | ~ v1_relat_1(A_268) ) ),
    inference(resolution,[status(thm)],[c_389,c_8])).

tff(c_401,plain,(
    ! [A_270] :
      ( k7_relat_1(A_270,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_270) ) ),
    inference(resolution,[status(thm)],[c_6,c_394])).

tff(c_412,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_366,c_401])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_365,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_358])).

tff(c_413,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_365,c_401])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_56,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_428,plain,(
    ! [A_271,B_272] :
      ( r1_xboole_0(A_271,B_272)
      | ~ r1_subset_1(A_271,B_272)
      | v1_xboole_0(B_272)
      | v1_xboole_0(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_601,plain,(
    ! [A_290,B_291] :
      ( k3_xboole_0(A_290,B_291) = k1_xboole_0
      | ~ r1_subset_1(A_290,B_291)
      | v1_xboole_0(B_291)
      | v1_xboole_0(A_290) ) ),
    inference(resolution,[status(thm)],[c_428,c_2])).

tff(c_604,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_601])).

tff(c_607,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_60,c_604])).

tff(c_522,plain,(
    ! [A_277,B_278,C_279] :
      ( k9_subset_1(A_277,B_278,C_279) = k3_xboole_0(B_278,C_279)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(A_277)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_534,plain,(
    ! [B_278] : k9_subset_1('#skF_1',B_278,'#skF_4') = k3_xboole_0(B_278,'#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_522])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_46,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_1413,plain,(
    ! [F_467,B_470,D_469,A_466,C_468,E_471] :
      ( v1_funct_1(k1_tmap_1(A_466,B_470,C_468,D_469,E_471,F_467))
      | ~ m1_subset_1(F_467,k1_zfmisc_1(k2_zfmisc_1(D_469,B_470)))
      | ~ v1_funct_2(F_467,D_469,B_470)
      | ~ v1_funct_1(F_467)
      | ~ m1_subset_1(E_471,k1_zfmisc_1(k2_zfmisc_1(C_468,B_470)))
      | ~ v1_funct_2(E_471,C_468,B_470)
      | ~ v1_funct_1(E_471)
      | ~ m1_subset_1(D_469,k1_zfmisc_1(A_466))
      | v1_xboole_0(D_469)
      | ~ m1_subset_1(C_468,k1_zfmisc_1(A_466))
      | v1_xboole_0(C_468)
      | v1_xboole_0(B_470)
      | v1_xboole_0(A_466) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1415,plain,(
    ! [A_466,C_468,E_471] :
      ( v1_funct_1(k1_tmap_1(A_466,'#skF_2',C_468,'#skF_4',E_471,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_471,k1_zfmisc_1(k2_zfmisc_1(C_468,'#skF_2')))
      | ~ v1_funct_2(E_471,C_468,'#skF_2')
      | ~ v1_funct_1(E_471)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_466))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_468,k1_zfmisc_1(A_466))
      | v1_xboole_0(C_468)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_466) ) ),
    inference(resolution,[status(thm)],[c_44,c_1413])).

tff(c_1420,plain,(
    ! [A_466,C_468,E_471] :
      ( v1_funct_1(k1_tmap_1(A_466,'#skF_2',C_468,'#skF_4',E_471,'#skF_6'))
      | ~ m1_subset_1(E_471,k1_zfmisc_1(k2_zfmisc_1(C_468,'#skF_2')))
      | ~ v1_funct_2(E_471,C_468,'#skF_2')
      | ~ v1_funct_1(E_471)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_466))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_468,k1_zfmisc_1(A_466))
      | v1_xboole_0(C_468)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_466) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1415])).

tff(c_1426,plain,(
    ! [A_472,C_473,E_474] :
      ( v1_funct_1(k1_tmap_1(A_472,'#skF_2',C_473,'#skF_4',E_474,'#skF_6'))
      | ~ m1_subset_1(E_474,k1_zfmisc_1(k2_zfmisc_1(C_473,'#skF_2')))
      | ~ v1_funct_2(E_474,C_473,'#skF_2')
      | ~ v1_funct_1(E_474)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_472))
      | ~ m1_subset_1(C_473,k1_zfmisc_1(A_472))
      | v1_xboole_0(C_473)
      | v1_xboole_0(A_472) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_1420])).

tff(c_1430,plain,(
    ! [A_472] :
      ( v1_funct_1(k1_tmap_1(A_472,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_472))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_472))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_472) ) ),
    inference(resolution,[status(thm)],[c_50,c_1426])).

tff(c_1437,plain,(
    ! [A_472] :
      ( v1_funct_1(k1_tmap_1(A_472,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_472))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_472))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_472) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1430])).

tff(c_1446,plain,(
    ! [A_476] :
      ( v1_funct_1(k1_tmap_1(A_476,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_476))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_476))
      | v1_xboole_0(A_476) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1437])).

tff(c_1449,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_1446])).

tff(c_1452,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1449])).

tff(c_1453,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1452])).

tff(c_554,plain,(
    ! [A_282,B_283,C_284,D_285] :
      ( k2_partfun1(A_282,B_283,C_284,D_285) = k7_relat_1(C_284,D_285)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | ~ v1_funct_1(C_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_558,plain,(
    ! [D_285] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_285) = k7_relat_1('#skF_5',D_285)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_554])).

tff(c_564,plain,(
    ! [D_285] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_285) = k7_relat_1('#skF_5',D_285) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_558])).

tff(c_556,plain,(
    ! [D_285] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_285) = k7_relat_1('#skF_6',D_285)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_44,c_554])).

tff(c_561,plain,(
    ! [D_285] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_285) = k7_relat_1('#skF_6',D_285) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_556])).

tff(c_38,plain,(
    ! [A_152,C_154,D_155,F_157,E_156,B_153] :
      ( v1_funct_2(k1_tmap_1(A_152,B_153,C_154,D_155,E_156,F_157),k4_subset_1(A_152,C_154,D_155),B_153)
      | ~ m1_subset_1(F_157,k1_zfmisc_1(k2_zfmisc_1(D_155,B_153)))
      | ~ v1_funct_2(F_157,D_155,B_153)
      | ~ v1_funct_1(F_157)
      | ~ m1_subset_1(E_156,k1_zfmisc_1(k2_zfmisc_1(C_154,B_153)))
      | ~ v1_funct_2(E_156,C_154,B_153)
      | ~ v1_funct_1(E_156)
      | ~ m1_subset_1(D_155,k1_zfmisc_1(A_152))
      | v1_xboole_0(D_155)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(A_152))
      | v1_xboole_0(C_154)
      | v1_xboole_0(B_153)
      | v1_xboole_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_36,plain,(
    ! [A_152,C_154,D_155,F_157,E_156,B_153] :
      ( m1_subset_1(k1_tmap_1(A_152,B_153,C_154,D_155,E_156,F_157),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_152,C_154,D_155),B_153)))
      | ~ m1_subset_1(F_157,k1_zfmisc_1(k2_zfmisc_1(D_155,B_153)))
      | ~ v1_funct_2(F_157,D_155,B_153)
      | ~ v1_funct_1(F_157)
      | ~ m1_subset_1(E_156,k1_zfmisc_1(k2_zfmisc_1(C_154,B_153)))
      | ~ v1_funct_2(E_156,C_154,B_153)
      | ~ v1_funct_1(E_156)
      | ~ m1_subset_1(D_155,k1_zfmisc_1(A_152))
      | v1_xboole_0(D_155)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(A_152))
      | v1_xboole_0(C_154)
      | v1_xboole_0(B_153)
      | v1_xboole_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1677,plain,(
    ! [C_518,F_516,E_519,A_515,B_517,D_520] :
      ( k2_partfun1(k4_subset_1(A_515,C_518,D_520),B_517,k1_tmap_1(A_515,B_517,C_518,D_520,E_519,F_516),C_518) = E_519
      | ~ m1_subset_1(k1_tmap_1(A_515,B_517,C_518,D_520,E_519,F_516),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_515,C_518,D_520),B_517)))
      | ~ v1_funct_2(k1_tmap_1(A_515,B_517,C_518,D_520,E_519,F_516),k4_subset_1(A_515,C_518,D_520),B_517)
      | ~ v1_funct_1(k1_tmap_1(A_515,B_517,C_518,D_520,E_519,F_516))
      | k2_partfun1(D_520,B_517,F_516,k9_subset_1(A_515,C_518,D_520)) != k2_partfun1(C_518,B_517,E_519,k9_subset_1(A_515,C_518,D_520))
      | ~ m1_subset_1(F_516,k1_zfmisc_1(k2_zfmisc_1(D_520,B_517)))
      | ~ v1_funct_2(F_516,D_520,B_517)
      | ~ v1_funct_1(F_516)
      | ~ m1_subset_1(E_519,k1_zfmisc_1(k2_zfmisc_1(C_518,B_517)))
      | ~ v1_funct_2(E_519,C_518,B_517)
      | ~ v1_funct_1(E_519)
      | ~ m1_subset_1(D_520,k1_zfmisc_1(A_515))
      | v1_xboole_0(D_520)
      | ~ m1_subset_1(C_518,k1_zfmisc_1(A_515))
      | v1_xboole_0(C_518)
      | v1_xboole_0(B_517)
      | v1_xboole_0(A_515) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1887,plain,(
    ! [D_572,B_573,A_569,C_571,E_574,F_570] :
      ( k2_partfun1(k4_subset_1(A_569,C_571,D_572),B_573,k1_tmap_1(A_569,B_573,C_571,D_572,E_574,F_570),C_571) = E_574
      | ~ v1_funct_2(k1_tmap_1(A_569,B_573,C_571,D_572,E_574,F_570),k4_subset_1(A_569,C_571,D_572),B_573)
      | ~ v1_funct_1(k1_tmap_1(A_569,B_573,C_571,D_572,E_574,F_570))
      | k2_partfun1(D_572,B_573,F_570,k9_subset_1(A_569,C_571,D_572)) != k2_partfun1(C_571,B_573,E_574,k9_subset_1(A_569,C_571,D_572))
      | ~ m1_subset_1(F_570,k1_zfmisc_1(k2_zfmisc_1(D_572,B_573)))
      | ~ v1_funct_2(F_570,D_572,B_573)
      | ~ v1_funct_1(F_570)
      | ~ m1_subset_1(E_574,k1_zfmisc_1(k2_zfmisc_1(C_571,B_573)))
      | ~ v1_funct_2(E_574,C_571,B_573)
      | ~ v1_funct_1(E_574)
      | ~ m1_subset_1(D_572,k1_zfmisc_1(A_569))
      | v1_xboole_0(D_572)
      | ~ m1_subset_1(C_571,k1_zfmisc_1(A_569))
      | v1_xboole_0(C_571)
      | v1_xboole_0(B_573)
      | v1_xboole_0(A_569) ) ),
    inference(resolution,[status(thm)],[c_36,c_1677])).

tff(c_1891,plain,(
    ! [F_576,E_580,D_578,B_579,C_577,A_575] :
      ( k2_partfun1(k4_subset_1(A_575,C_577,D_578),B_579,k1_tmap_1(A_575,B_579,C_577,D_578,E_580,F_576),C_577) = E_580
      | ~ v1_funct_1(k1_tmap_1(A_575,B_579,C_577,D_578,E_580,F_576))
      | k2_partfun1(D_578,B_579,F_576,k9_subset_1(A_575,C_577,D_578)) != k2_partfun1(C_577,B_579,E_580,k9_subset_1(A_575,C_577,D_578))
      | ~ m1_subset_1(F_576,k1_zfmisc_1(k2_zfmisc_1(D_578,B_579)))
      | ~ v1_funct_2(F_576,D_578,B_579)
      | ~ v1_funct_1(F_576)
      | ~ m1_subset_1(E_580,k1_zfmisc_1(k2_zfmisc_1(C_577,B_579)))
      | ~ v1_funct_2(E_580,C_577,B_579)
      | ~ v1_funct_1(E_580)
      | ~ m1_subset_1(D_578,k1_zfmisc_1(A_575))
      | v1_xboole_0(D_578)
      | ~ m1_subset_1(C_577,k1_zfmisc_1(A_575))
      | v1_xboole_0(C_577)
      | v1_xboole_0(B_579)
      | v1_xboole_0(A_575) ) ),
    inference(resolution,[status(thm)],[c_38,c_1887])).

tff(c_1895,plain,(
    ! [A_575,C_577,E_580] :
      ( k2_partfun1(k4_subset_1(A_575,C_577,'#skF_4'),'#skF_2',k1_tmap_1(A_575,'#skF_2',C_577,'#skF_4',E_580,'#skF_6'),C_577) = E_580
      | ~ v1_funct_1(k1_tmap_1(A_575,'#skF_2',C_577,'#skF_4',E_580,'#skF_6'))
      | k2_partfun1(C_577,'#skF_2',E_580,k9_subset_1(A_575,C_577,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_575,C_577,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_580,k1_zfmisc_1(k2_zfmisc_1(C_577,'#skF_2')))
      | ~ v1_funct_2(E_580,C_577,'#skF_2')
      | ~ v1_funct_1(E_580)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_575))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_577,k1_zfmisc_1(A_575))
      | v1_xboole_0(C_577)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_575) ) ),
    inference(resolution,[status(thm)],[c_44,c_1891])).

tff(c_1901,plain,(
    ! [A_575,C_577,E_580] :
      ( k2_partfun1(k4_subset_1(A_575,C_577,'#skF_4'),'#skF_2',k1_tmap_1(A_575,'#skF_2',C_577,'#skF_4',E_580,'#skF_6'),C_577) = E_580
      | ~ v1_funct_1(k1_tmap_1(A_575,'#skF_2',C_577,'#skF_4',E_580,'#skF_6'))
      | k2_partfun1(C_577,'#skF_2',E_580,k9_subset_1(A_575,C_577,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_575,C_577,'#skF_4'))
      | ~ m1_subset_1(E_580,k1_zfmisc_1(k2_zfmisc_1(C_577,'#skF_2')))
      | ~ v1_funct_2(E_580,C_577,'#skF_2')
      | ~ v1_funct_1(E_580)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_575))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_577,k1_zfmisc_1(A_575))
      | v1_xboole_0(C_577)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_575) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_561,c_1895])).

tff(c_1911,plain,(
    ! [A_587,C_588,E_589] :
      ( k2_partfun1(k4_subset_1(A_587,C_588,'#skF_4'),'#skF_2',k1_tmap_1(A_587,'#skF_2',C_588,'#skF_4',E_589,'#skF_6'),C_588) = E_589
      | ~ v1_funct_1(k1_tmap_1(A_587,'#skF_2',C_588,'#skF_4',E_589,'#skF_6'))
      | k2_partfun1(C_588,'#skF_2',E_589,k9_subset_1(A_587,C_588,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_587,C_588,'#skF_4'))
      | ~ m1_subset_1(E_589,k1_zfmisc_1(k2_zfmisc_1(C_588,'#skF_2')))
      | ~ v1_funct_2(E_589,C_588,'#skF_2')
      | ~ v1_funct_1(E_589)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_587))
      | ~ m1_subset_1(C_588,k1_zfmisc_1(A_587))
      | v1_xboole_0(C_588)
      | v1_xboole_0(A_587) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_1901])).

tff(c_1918,plain,(
    ! [A_587] :
      ( k2_partfun1(k4_subset_1(A_587,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_587,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_587,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_587,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_587,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_587))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_587))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_587) ) ),
    inference(resolution,[status(thm)],[c_50,c_1911])).

tff(c_1928,plain,(
    ! [A_587] :
      ( k2_partfun1(k4_subset_1(A_587,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_587,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_587,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_587,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_587,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_587))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_587))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_587) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_564,c_1918])).

tff(c_1983,plain,(
    ! [A_592] :
      ( k2_partfun1(k4_subset_1(A_592,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_592,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_592,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_592,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_592,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_592))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_592))
      | v1_xboole_0(A_592) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1928])).

tff(c_666,plain,(
    ! [B_301,C_299,E_302,D_300,F_298,A_297] :
      ( v1_funct_1(k1_tmap_1(A_297,B_301,C_299,D_300,E_302,F_298))
      | ~ m1_subset_1(F_298,k1_zfmisc_1(k2_zfmisc_1(D_300,B_301)))
      | ~ v1_funct_2(F_298,D_300,B_301)
      | ~ v1_funct_1(F_298)
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(C_299,B_301)))
      | ~ v1_funct_2(E_302,C_299,B_301)
      | ~ v1_funct_1(E_302)
      | ~ m1_subset_1(D_300,k1_zfmisc_1(A_297))
      | v1_xboole_0(D_300)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(A_297))
      | v1_xboole_0(C_299)
      | v1_xboole_0(B_301)
      | v1_xboole_0(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_668,plain,(
    ! [A_297,C_299,E_302] :
      ( v1_funct_1(k1_tmap_1(A_297,'#skF_2',C_299,'#skF_4',E_302,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(C_299,'#skF_2')))
      | ~ v1_funct_2(E_302,C_299,'#skF_2')
      | ~ v1_funct_1(E_302)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_297))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_299,k1_zfmisc_1(A_297))
      | v1_xboole_0(C_299)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_297) ) ),
    inference(resolution,[status(thm)],[c_44,c_666])).

tff(c_673,plain,(
    ! [A_297,C_299,E_302] :
      ( v1_funct_1(k1_tmap_1(A_297,'#skF_2',C_299,'#skF_4',E_302,'#skF_6'))
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(C_299,'#skF_2')))
      | ~ v1_funct_2(E_302,C_299,'#skF_2')
      | ~ v1_funct_1(E_302)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_297))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_299,k1_zfmisc_1(A_297))
      | v1_xboole_0(C_299)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_297) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_668])).

tff(c_679,plain,(
    ! [A_303,C_304,E_305] :
      ( v1_funct_1(k1_tmap_1(A_303,'#skF_2',C_304,'#skF_4',E_305,'#skF_6'))
      | ~ m1_subset_1(E_305,k1_zfmisc_1(k2_zfmisc_1(C_304,'#skF_2')))
      | ~ v1_funct_2(E_305,C_304,'#skF_2')
      | ~ v1_funct_1(E_305)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_303))
      | ~ m1_subset_1(C_304,k1_zfmisc_1(A_303))
      | v1_xboole_0(C_304)
      | v1_xboole_0(A_303) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_673])).

tff(c_683,plain,(
    ! [A_303] :
      ( v1_funct_1(k1_tmap_1(A_303,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_303))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_303))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_303) ) ),
    inference(resolution,[status(thm)],[c_50,c_679])).

tff(c_690,plain,(
    ! [A_303] :
      ( v1_funct_1(k1_tmap_1(A_303,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_303))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_303))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_683])).

tff(c_699,plain,(
    ! [A_307] :
      ( v1_funct_1(k1_tmap_1(A_307,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_307))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_307))
      | v1_xboole_0(A_307) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_690])).

tff(c_702,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_699])).

tff(c_705,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_702])).

tff(c_706,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_705])).

tff(c_836,plain,(
    ! [E_339,C_338,F_336,D_340,B_337,A_335] :
      ( k2_partfun1(k4_subset_1(A_335,C_338,D_340),B_337,k1_tmap_1(A_335,B_337,C_338,D_340,E_339,F_336),D_340) = F_336
      | ~ m1_subset_1(k1_tmap_1(A_335,B_337,C_338,D_340,E_339,F_336),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_335,C_338,D_340),B_337)))
      | ~ v1_funct_2(k1_tmap_1(A_335,B_337,C_338,D_340,E_339,F_336),k4_subset_1(A_335,C_338,D_340),B_337)
      | ~ v1_funct_1(k1_tmap_1(A_335,B_337,C_338,D_340,E_339,F_336))
      | k2_partfun1(D_340,B_337,F_336,k9_subset_1(A_335,C_338,D_340)) != k2_partfun1(C_338,B_337,E_339,k9_subset_1(A_335,C_338,D_340))
      | ~ m1_subset_1(F_336,k1_zfmisc_1(k2_zfmisc_1(D_340,B_337)))
      | ~ v1_funct_2(F_336,D_340,B_337)
      | ~ v1_funct_1(F_336)
      | ~ m1_subset_1(E_339,k1_zfmisc_1(k2_zfmisc_1(C_338,B_337)))
      | ~ v1_funct_2(E_339,C_338,B_337)
      | ~ v1_funct_1(E_339)
      | ~ m1_subset_1(D_340,k1_zfmisc_1(A_335))
      | v1_xboole_0(D_340)
      | ~ m1_subset_1(C_338,k1_zfmisc_1(A_335))
      | v1_xboole_0(C_338)
      | v1_xboole_0(B_337)
      | v1_xboole_0(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1167,plain,(
    ! [D_426,F_424,C_425,B_427,A_423,E_428] :
      ( k2_partfun1(k4_subset_1(A_423,C_425,D_426),B_427,k1_tmap_1(A_423,B_427,C_425,D_426,E_428,F_424),D_426) = F_424
      | ~ v1_funct_2(k1_tmap_1(A_423,B_427,C_425,D_426,E_428,F_424),k4_subset_1(A_423,C_425,D_426),B_427)
      | ~ v1_funct_1(k1_tmap_1(A_423,B_427,C_425,D_426,E_428,F_424))
      | k2_partfun1(D_426,B_427,F_424,k9_subset_1(A_423,C_425,D_426)) != k2_partfun1(C_425,B_427,E_428,k9_subset_1(A_423,C_425,D_426))
      | ~ m1_subset_1(F_424,k1_zfmisc_1(k2_zfmisc_1(D_426,B_427)))
      | ~ v1_funct_2(F_424,D_426,B_427)
      | ~ v1_funct_1(F_424)
      | ~ m1_subset_1(E_428,k1_zfmisc_1(k2_zfmisc_1(C_425,B_427)))
      | ~ v1_funct_2(E_428,C_425,B_427)
      | ~ v1_funct_1(E_428)
      | ~ m1_subset_1(D_426,k1_zfmisc_1(A_423))
      | v1_xboole_0(D_426)
      | ~ m1_subset_1(C_425,k1_zfmisc_1(A_423))
      | v1_xboole_0(C_425)
      | v1_xboole_0(B_427)
      | v1_xboole_0(A_423) ) ),
    inference(resolution,[status(thm)],[c_36,c_836])).

tff(c_1339,plain,(
    ! [B_451,F_448,E_452,A_447,D_450,C_449] :
      ( k2_partfun1(k4_subset_1(A_447,C_449,D_450),B_451,k1_tmap_1(A_447,B_451,C_449,D_450,E_452,F_448),D_450) = F_448
      | ~ v1_funct_1(k1_tmap_1(A_447,B_451,C_449,D_450,E_452,F_448))
      | k2_partfun1(D_450,B_451,F_448,k9_subset_1(A_447,C_449,D_450)) != k2_partfun1(C_449,B_451,E_452,k9_subset_1(A_447,C_449,D_450))
      | ~ m1_subset_1(F_448,k1_zfmisc_1(k2_zfmisc_1(D_450,B_451)))
      | ~ v1_funct_2(F_448,D_450,B_451)
      | ~ v1_funct_1(F_448)
      | ~ m1_subset_1(E_452,k1_zfmisc_1(k2_zfmisc_1(C_449,B_451)))
      | ~ v1_funct_2(E_452,C_449,B_451)
      | ~ v1_funct_1(E_452)
      | ~ m1_subset_1(D_450,k1_zfmisc_1(A_447))
      | v1_xboole_0(D_450)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(A_447))
      | v1_xboole_0(C_449)
      | v1_xboole_0(B_451)
      | v1_xboole_0(A_447) ) ),
    inference(resolution,[status(thm)],[c_38,c_1167])).

tff(c_1343,plain,(
    ! [A_447,C_449,E_452] :
      ( k2_partfun1(k4_subset_1(A_447,C_449,'#skF_4'),'#skF_2',k1_tmap_1(A_447,'#skF_2',C_449,'#skF_4',E_452,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_447,'#skF_2',C_449,'#skF_4',E_452,'#skF_6'))
      | k2_partfun1(C_449,'#skF_2',E_452,k9_subset_1(A_447,C_449,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_447,C_449,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_452,k1_zfmisc_1(k2_zfmisc_1(C_449,'#skF_2')))
      | ~ v1_funct_2(E_452,C_449,'#skF_2')
      | ~ v1_funct_1(E_452)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_447))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_449,k1_zfmisc_1(A_447))
      | v1_xboole_0(C_449)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_447) ) ),
    inference(resolution,[status(thm)],[c_44,c_1339])).

tff(c_1349,plain,(
    ! [A_447,C_449,E_452] :
      ( k2_partfun1(k4_subset_1(A_447,C_449,'#skF_4'),'#skF_2',k1_tmap_1(A_447,'#skF_2',C_449,'#skF_4',E_452,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_447,'#skF_2',C_449,'#skF_4',E_452,'#skF_6'))
      | k2_partfun1(C_449,'#skF_2',E_452,k9_subset_1(A_447,C_449,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_447,C_449,'#skF_4'))
      | ~ m1_subset_1(E_452,k1_zfmisc_1(k2_zfmisc_1(C_449,'#skF_2')))
      | ~ v1_funct_2(E_452,C_449,'#skF_2')
      | ~ v1_funct_1(E_452)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_447))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_449,k1_zfmisc_1(A_447))
      | v1_xboole_0(C_449)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_447) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_561,c_1343])).

tff(c_1355,plain,(
    ! [A_453,C_454,E_455] :
      ( k2_partfun1(k4_subset_1(A_453,C_454,'#skF_4'),'#skF_2',k1_tmap_1(A_453,'#skF_2',C_454,'#skF_4',E_455,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_453,'#skF_2',C_454,'#skF_4',E_455,'#skF_6'))
      | k2_partfun1(C_454,'#skF_2',E_455,k9_subset_1(A_453,C_454,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_453,C_454,'#skF_4'))
      | ~ m1_subset_1(E_455,k1_zfmisc_1(k2_zfmisc_1(C_454,'#skF_2')))
      | ~ v1_funct_2(E_455,C_454,'#skF_2')
      | ~ v1_funct_1(E_455)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_453))
      | ~ m1_subset_1(C_454,k1_zfmisc_1(A_453))
      | v1_xboole_0(C_454)
      | v1_xboole_0(A_453) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_1349])).

tff(c_1362,plain,(
    ! [A_453] :
      ( k2_partfun1(k4_subset_1(A_453,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_453,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_453,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_453,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_453,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_453))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_453))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_453) ) ),
    inference(resolution,[status(thm)],[c_50,c_1355])).

tff(c_1372,plain,(
    ! [A_453] :
      ( k2_partfun1(k4_subset_1(A_453,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_453,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_453,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_453,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_453,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_453))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_453))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_453) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_564,c_1362])).

tff(c_1379,plain,(
    ! [A_465] :
      ( k2_partfun1(k4_subset_1(A_465,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_465,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_465,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_465,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_465,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_465))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_465))
      | v1_xboole_0(A_465) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1372])).

tff(c_100,plain,(
    ! [C_224,A_225,B_226] :
      ( v1_relat_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_107,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_100])).

tff(c_131,plain,(
    ! [A_231,B_232] :
      ( v1_xboole_0(k7_relat_1(A_231,B_232))
      | ~ v1_xboole_0(B_232)
      | ~ v1_relat_1(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_136,plain,(
    ! [A_233,B_234] :
      ( k7_relat_1(A_233,B_234) = k1_xboole_0
      | ~ v1_xboole_0(B_234)
      | ~ v1_relat_1(A_233) ) ),
    inference(resolution,[status(thm)],[c_131,c_8])).

tff(c_143,plain,(
    ! [A_235] :
      ( k7_relat_1(A_235,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_235) ) ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_155,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_107,c_143])).

tff(c_108,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_100])).

tff(c_154,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_108,c_143])).

tff(c_174,plain,(
    ! [A_236,B_237] :
      ( r1_xboole_0(A_236,B_237)
      | ~ r1_subset_1(A_236,B_237)
      | v1_xboole_0(B_237)
      | v1_xboole_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_341,plain,(
    ! [A_257,B_258] :
      ( k3_xboole_0(A_257,B_258) = k1_xboole_0
      | ~ r1_subset_1(A_257,B_258)
      | v1_xboole_0(B_258)
      | v1_xboole_0(A_257) ) ),
    inference(resolution,[status(thm)],[c_174,c_2])).

tff(c_347,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_341])).

tff(c_351,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_60,c_347])).

tff(c_310,plain,(
    ! [A_249,B_250,C_251,D_252] :
      ( k2_partfun1(A_249,B_250,C_251,D_252) = k7_relat_1(C_251,D_252)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250)))
      | ~ v1_funct_1(C_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_314,plain,(
    ! [D_252] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_252) = k7_relat_1('#skF_5',D_252)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_310])).

tff(c_320,plain,(
    ! [D_252] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_252) = k7_relat_1('#skF_5',D_252) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_314])).

tff(c_312,plain,(
    ! [D_252] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_252) = k7_relat_1('#skF_6',D_252)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_44,c_310])).

tff(c_317,plain,(
    ! [D_252] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_252) = k7_relat_1('#skF_6',D_252) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_312])).

tff(c_216,plain,(
    ! [A_240,B_241,C_242] :
      ( k9_subset_1(A_240,B_241,C_242) = k3_xboole_0(B_241,C_242)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(A_240)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_228,plain,(
    ! [B_241] : k9_subset_1('#skF_1',B_241,'#skF_4') = k3_xboole_0(B_241,'#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_216])).

tff(c_42,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_99,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_238,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_228,c_99])).

tff(c_340,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_317,c_238])).

tff(c_352,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_351,c_340])).

tff(c_355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_154,c_352])).

tff(c_356,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_665,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_1390,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1379,c_665])).

tff(c_1404,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_413,c_607,c_412,c_607,c_534,c_534,c_706,c_1390])).

tff(c_1406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1404])).

tff(c_1407,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_1992,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1983,c_1407])).

tff(c_2003,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_412,c_413,c_607,c_534,c_607,c_534,c_1453,c_1992])).

tff(c_2005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2003])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:41:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.15/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.26/2.17  
% 6.26/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.26/2.17  %$ v1_funct_2 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k2_enumset1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.26/2.17  
% 6.26/2.17  %Foreground sorts:
% 6.26/2.17  
% 6.26/2.17  
% 6.26/2.17  %Background operators:
% 6.26/2.17  
% 6.26/2.17  
% 6.26/2.17  %Foreground operators:
% 6.26/2.17  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 6.26/2.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.26/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.26/2.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.26/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.26/2.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.26/2.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.26/2.17  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.26/2.17  tff('#skF_5', type, '#skF_5': $i).
% 6.26/2.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.26/2.17  tff('#skF_6', type, '#skF_6': $i).
% 6.26/2.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.26/2.17  tff('#skF_2', type, '#skF_2': $i).
% 6.26/2.17  tff('#skF_3', type, '#skF_3': $i).
% 6.26/2.17  tff('#skF_1', type, '#skF_1': $i).
% 6.26/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.26/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.26/2.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.26/2.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.26/2.17  tff('#skF_4', type, '#skF_4': $i).
% 6.26/2.17  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.26/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.26/2.17  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.26/2.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.26/2.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.26/2.17  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.26/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.26/2.17  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.26/2.17  
% 6.26/2.20  tff(f_201, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 6.26/2.20  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.26/2.20  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.26/2.20  tff(f_57, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc16_relat_1)).
% 6.26/2.20  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.26/2.20  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 6.26/2.20  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.26/2.20  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.26/2.20  tff(f_159, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 6.26/2.20  tff(f_77, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.26/2.20  tff(f_125, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 6.26/2.20  tff(c_68, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.26/2.20  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.26/2.20  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.26/2.20  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.26/2.20  tff(c_358, plain, (![C_259, A_260, B_261]: (v1_relat_1(C_259) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.26/2.20  tff(c_366, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_358])).
% 6.26/2.20  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.26/2.20  tff(c_389, plain, (![A_266, B_267]: (v1_xboole_0(k7_relat_1(A_266, B_267)) | ~v1_xboole_0(B_267) | ~v1_relat_1(A_266))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.26/2.20  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.26/2.20  tff(c_394, plain, (![A_268, B_269]: (k7_relat_1(A_268, B_269)=k1_xboole_0 | ~v1_xboole_0(B_269) | ~v1_relat_1(A_268))), inference(resolution, [status(thm)], [c_389, c_8])).
% 6.26/2.20  tff(c_401, plain, (![A_270]: (k7_relat_1(A_270, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_270))), inference(resolution, [status(thm)], [c_6, c_394])).
% 6.26/2.20  tff(c_412, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_366, c_401])).
% 6.26/2.20  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.26/2.20  tff(c_365, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_358])).
% 6.26/2.20  tff(c_413, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_365, c_401])).
% 6.26/2.20  tff(c_64, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.26/2.20  tff(c_60, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.26/2.20  tff(c_56, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.26/2.20  tff(c_428, plain, (![A_271, B_272]: (r1_xboole_0(A_271, B_272) | ~r1_subset_1(A_271, B_272) | v1_xboole_0(B_272) | v1_xboole_0(A_271))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.26/2.20  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.26/2.20  tff(c_601, plain, (![A_290, B_291]: (k3_xboole_0(A_290, B_291)=k1_xboole_0 | ~r1_subset_1(A_290, B_291) | v1_xboole_0(B_291) | v1_xboole_0(A_290))), inference(resolution, [status(thm)], [c_428, c_2])).
% 6.26/2.20  tff(c_604, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_601])).
% 6.26/2.20  tff(c_607, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_60, c_604])).
% 6.26/2.20  tff(c_522, plain, (![A_277, B_278, C_279]: (k9_subset_1(A_277, B_278, C_279)=k3_xboole_0(B_278, C_279) | ~m1_subset_1(C_279, k1_zfmisc_1(A_277)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.26/2.20  tff(c_534, plain, (![B_278]: (k9_subset_1('#skF_1', B_278, '#skF_4')=k3_xboole_0(B_278, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_522])).
% 6.26/2.20  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.26/2.20  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.26/2.20  tff(c_66, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.26/2.20  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.26/2.20  tff(c_46, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.26/2.20  tff(c_1413, plain, (![F_467, B_470, D_469, A_466, C_468, E_471]: (v1_funct_1(k1_tmap_1(A_466, B_470, C_468, D_469, E_471, F_467)) | ~m1_subset_1(F_467, k1_zfmisc_1(k2_zfmisc_1(D_469, B_470))) | ~v1_funct_2(F_467, D_469, B_470) | ~v1_funct_1(F_467) | ~m1_subset_1(E_471, k1_zfmisc_1(k2_zfmisc_1(C_468, B_470))) | ~v1_funct_2(E_471, C_468, B_470) | ~v1_funct_1(E_471) | ~m1_subset_1(D_469, k1_zfmisc_1(A_466)) | v1_xboole_0(D_469) | ~m1_subset_1(C_468, k1_zfmisc_1(A_466)) | v1_xboole_0(C_468) | v1_xboole_0(B_470) | v1_xboole_0(A_466))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.26/2.20  tff(c_1415, plain, (![A_466, C_468, E_471]: (v1_funct_1(k1_tmap_1(A_466, '#skF_2', C_468, '#skF_4', E_471, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_471, k1_zfmisc_1(k2_zfmisc_1(C_468, '#skF_2'))) | ~v1_funct_2(E_471, C_468, '#skF_2') | ~v1_funct_1(E_471) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_466)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_468, k1_zfmisc_1(A_466)) | v1_xboole_0(C_468) | v1_xboole_0('#skF_2') | v1_xboole_0(A_466))), inference(resolution, [status(thm)], [c_44, c_1413])).
% 6.26/2.20  tff(c_1420, plain, (![A_466, C_468, E_471]: (v1_funct_1(k1_tmap_1(A_466, '#skF_2', C_468, '#skF_4', E_471, '#skF_6')) | ~m1_subset_1(E_471, k1_zfmisc_1(k2_zfmisc_1(C_468, '#skF_2'))) | ~v1_funct_2(E_471, C_468, '#skF_2') | ~v1_funct_1(E_471) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_466)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_468, k1_zfmisc_1(A_466)) | v1_xboole_0(C_468) | v1_xboole_0('#skF_2') | v1_xboole_0(A_466))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1415])).
% 6.26/2.20  tff(c_1426, plain, (![A_472, C_473, E_474]: (v1_funct_1(k1_tmap_1(A_472, '#skF_2', C_473, '#skF_4', E_474, '#skF_6')) | ~m1_subset_1(E_474, k1_zfmisc_1(k2_zfmisc_1(C_473, '#skF_2'))) | ~v1_funct_2(E_474, C_473, '#skF_2') | ~v1_funct_1(E_474) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_472)) | ~m1_subset_1(C_473, k1_zfmisc_1(A_472)) | v1_xboole_0(C_473) | v1_xboole_0(A_472))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_1420])).
% 6.26/2.20  tff(c_1430, plain, (![A_472]: (v1_funct_1(k1_tmap_1(A_472, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_472)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_472)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_472))), inference(resolution, [status(thm)], [c_50, c_1426])).
% 6.26/2.20  tff(c_1437, plain, (![A_472]: (v1_funct_1(k1_tmap_1(A_472, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_472)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_472)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_472))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1430])).
% 6.26/2.20  tff(c_1446, plain, (![A_476]: (v1_funct_1(k1_tmap_1(A_476, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_476)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_476)) | v1_xboole_0(A_476))), inference(negUnitSimplification, [status(thm)], [c_64, c_1437])).
% 6.26/2.20  tff(c_1449, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_1446])).
% 6.26/2.20  tff(c_1452, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1449])).
% 6.26/2.20  tff(c_1453, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1452])).
% 6.26/2.20  tff(c_554, plain, (![A_282, B_283, C_284, D_285]: (k2_partfun1(A_282, B_283, C_284, D_285)=k7_relat_1(C_284, D_285) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | ~v1_funct_1(C_284))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.26/2.20  tff(c_558, plain, (![D_285]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_285)=k7_relat_1('#skF_5', D_285) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_554])).
% 6.26/2.20  tff(c_564, plain, (![D_285]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_285)=k7_relat_1('#skF_5', D_285))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_558])).
% 6.26/2.20  tff(c_556, plain, (![D_285]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_285)=k7_relat_1('#skF_6', D_285) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_554])).
% 6.26/2.20  tff(c_561, plain, (![D_285]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_285)=k7_relat_1('#skF_6', D_285))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_556])).
% 6.26/2.20  tff(c_38, plain, (![A_152, C_154, D_155, F_157, E_156, B_153]: (v1_funct_2(k1_tmap_1(A_152, B_153, C_154, D_155, E_156, F_157), k4_subset_1(A_152, C_154, D_155), B_153) | ~m1_subset_1(F_157, k1_zfmisc_1(k2_zfmisc_1(D_155, B_153))) | ~v1_funct_2(F_157, D_155, B_153) | ~v1_funct_1(F_157) | ~m1_subset_1(E_156, k1_zfmisc_1(k2_zfmisc_1(C_154, B_153))) | ~v1_funct_2(E_156, C_154, B_153) | ~v1_funct_1(E_156) | ~m1_subset_1(D_155, k1_zfmisc_1(A_152)) | v1_xboole_0(D_155) | ~m1_subset_1(C_154, k1_zfmisc_1(A_152)) | v1_xboole_0(C_154) | v1_xboole_0(B_153) | v1_xboole_0(A_152))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.26/2.20  tff(c_36, plain, (![A_152, C_154, D_155, F_157, E_156, B_153]: (m1_subset_1(k1_tmap_1(A_152, B_153, C_154, D_155, E_156, F_157), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_152, C_154, D_155), B_153))) | ~m1_subset_1(F_157, k1_zfmisc_1(k2_zfmisc_1(D_155, B_153))) | ~v1_funct_2(F_157, D_155, B_153) | ~v1_funct_1(F_157) | ~m1_subset_1(E_156, k1_zfmisc_1(k2_zfmisc_1(C_154, B_153))) | ~v1_funct_2(E_156, C_154, B_153) | ~v1_funct_1(E_156) | ~m1_subset_1(D_155, k1_zfmisc_1(A_152)) | v1_xboole_0(D_155) | ~m1_subset_1(C_154, k1_zfmisc_1(A_152)) | v1_xboole_0(C_154) | v1_xboole_0(B_153) | v1_xboole_0(A_152))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.26/2.20  tff(c_1677, plain, (![C_518, F_516, E_519, A_515, B_517, D_520]: (k2_partfun1(k4_subset_1(A_515, C_518, D_520), B_517, k1_tmap_1(A_515, B_517, C_518, D_520, E_519, F_516), C_518)=E_519 | ~m1_subset_1(k1_tmap_1(A_515, B_517, C_518, D_520, E_519, F_516), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_515, C_518, D_520), B_517))) | ~v1_funct_2(k1_tmap_1(A_515, B_517, C_518, D_520, E_519, F_516), k4_subset_1(A_515, C_518, D_520), B_517) | ~v1_funct_1(k1_tmap_1(A_515, B_517, C_518, D_520, E_519, F_516)) | k2_partfun1(D_520, B_517, F_516, k9_subset_1(A_515, C_518, D_520))!=k2_partfun1(C_518, B_517, E_519, k9_subset_1(A_515, C_518, D_520)) | ~m1_subset_1(F_516, k1_zfmisc_1(k2_zfmisc_1(D_520, B_517))) | ~v1_funct_2(F_516, D_520, B_517) | ~v1_funct_1(F_516) | ~m1_subset_1(E_519, k1_zfmisc_1(k2_zfmisc_1(C_518, B_517))) | ~v1_funct_2(E_519, C_518, B_517) | ~v1_funct_1(E_519) | ~m1_subset_1(D_520, k1_zfmisc_1(A_515)) | v1_xboole_0(D_520) | ~m1_subset_1(C_518, k1_zfmisc_1(A_515)) | v1_xboole_0(C_518) | v1_xboole_0(B_517) | v1_xboole_0(A_515))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.26/2.20  tff(c_1887, plain, (![D_572, B_573, A_569, C_571, E_574, F_570]: (k2_partfun1(k4_subset_1(A_569, C_571, D_572), B_573, k1_tmap_1(A_569, B_573, C_571, D_572, E_574, F_570), C_571)=E_574 | ~v1_funct_2(k1_tmap_1(A_569, B_573, C_571, D_572, E_574, F_570), k4_subset_1(A_569, C_571, D_572), B_573) | ~v1_funct_1(k1_tmap_1(A_569, B_573, C_571, D_572, E_574, F_570)) | k2_partfun1(D_572, B_573, F_570, k9_subset_1(A_569, C_571, D_572))!=k2_partfun1(C_571, B_573, E_574, k9_subset_1(A_569, C_571, D_572)) | ~m1_subset_1(F_570, k1_zfmisc_1(k2_zfmisc_1(D_572, B_573))) | ~v1_funct_2(F_570, D_572, B_573) | ~v1_funct_1(F_570) | ~m1_subset_1(E_574, k1_zfmisc_1(k2_zfmisc_1(C_571, B_573))) | ~v1_funct_2(E_574, C_571, B_573) | ~v1_funct_1(E_574) | ~m1_subset_1(D_572, k1_zfmisc_1(A_569)) | v1_xboole_0(D_572) | ~m1_subset_1(C_571, k1_zfmisc_1(A_569)) | v1_xboole_0(C_571) | v1_xboole_0(B_573) | v1_xboole_0(A_569))), inference(resolution, [status(thm)], [c_36, c_1677])).
% 6.26/2.20  tff(c_1891, plain, (![F_576, E_580, D_578, B_579, C_577, A_575]: (k2_partfun1(k4_subset_1(A_575, C_577, D_578), B_579, k1_tmap_1(A_575, B_579, C_577, D_578, E_580, F_576), C_577)=E_580 | ~v1_funct_1(k1_tmap_1(A_575, B_579, C_577, D_578, E_580, F_576)) | k2_partfun1(D_578, B_579, F_576, k9_subset_1(A_575, C_577, D_578))!=k2_partfun1(C_577, B_579, E_580, k9_subset_1(A_575, C_577, D_578)) | ~m1_subset_1(F_576, k1_zfmisc_1(k2_zfmisc_1(D_578, B_579))) | ~v1_funct_2(F_576, D_578, B_579) | ~v1_funct_1(F_576) | ~m1_subset_1(E_580, k1_zfmisc_1(k2_zfmisc_1(C_577, B_579))) | ~v1_funct_2(E_580, C_577, B_579) | ~v1_funct_1(E_580) | ~m1_subset_1(D_578, k1_zfmisc_1(A_575)) | v1_xboole_0(D_578) | ~m1_subset_1(C_577, k1_zfmisc_1(A_575)) | v1_xboole_0(C_577) | v1_xboole_0(B_579) | v1_xboole_0(A_575))), inference(resolution, [status(thm)], [c_38, c_1887])).
% 6.26/2.20  tff(c_1895, plain, (![A_575, C_577, E_580]: (k2_partfun1(k4_subset_1(A_575, C_577, '#skF_4'), '#skF_2', k1_tmap_1(A_575, '#skF_2', C_577, '#skF_4', E_580, '#skF_6'), C_577)=E_580 | ~v1_funct_1(k1_tmap_1(A_575, '#skF_2', C_577, '#skF_4', E_580, '#skF_6')) | k2_partfun1(C_577, '#skF_2', E_580, k9_subset_1(A_575, C_577, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_575, C_577, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_580, k1_zfmisc_1(k2_zfmisc_1(C_577, '#skF_2'))) | ~v1_funct_2(E_580, C_577, '#skF_2') | ~v1_funct_1(E_580) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_575)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_577, k1_zfmisc_1(A_575)) | v1_xboole_0(C_577) | v1_xboole_0('#skF_2') | v1_xboole_0(A_575))), inference(resolution, [status(thm)], [c_44, c_1891])).
% 6.26/2.20  tff(c_1901, plain, (![A_575, C_577, E_580]: (k2_partfun1(k4_subset_1(A_575, C_577, '#skF_4'), '#skF_2', k1_tmap_1(A_575, '#skF_2', C_577, '#skF_4', E_580, '#skF_6'), C_577)=E_580 | ~v1_funct_1(k1_tmap_1(A_575, '#skF_2', C_577, '#skF_4', E_580, '#skF_6')) | k2_partfun1(C_577, '#skF_2', E_580, k9_subset_1(A_575, C_577, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_575, C_577, '#skF_4')) | ~m1_subset_1(E_580, k1_zfmisc_1(k2_zfmisc_1(C_577, '#skF_2'))) | ~v1_funct_2(E_580, C_577, '#skF_2') | ~v1_funct_1(E_580) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_575)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_577, k1_zfmisc_1(A_575)) | v1_xboole_0(C_577) | v1_xboole_0('#skF_2') | v1_xboole_0(A_575))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_561, c_1895])).
% 6.26/2.20  tff(c_1911, plain, (![A_587, C_588, E_589]: (k2_partfun1(k4_subset_1(A_587, C_588, '#skF_4'), '#skF_2', k1_tmap_1(A_587, '#skF_2', C_588, '#skF_4', E_589, '#skF_6'), C_588)=E_589 | ~v1_funct_1(k1_tmap_1(A_587, '#skF_2', C_588, '#skF_4', E_589, '#skF_6')) | k2_partfun1(C_588, '#skF_2', E_589, k9_subset_1(A_587, C_588, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_587, C_588, '#skF_4')) | ~m1_subset_1(E_589, k1_zfmisc_1(k2_zfmisc_1(C_588, '#skF_2'))) | ~v1_funct_2(E_589, C_588, '#skF_2') | ~v1_funct_1(E_589) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_587)) | ~m1_subset_1(C_588, k1_zfmisc_1(A_587)) | v1_xboole_0(C_588) | v1_xboole_0(A_587))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_1901])).
% 6.26/2.20  tff(c_1918, plain, (![A_587]: (k2_partfun1(k4_subset_1(A_587, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_587, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_587, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_587, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_587, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_587)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_587)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_587))), inference(resolution, [status(thm)], [c_50, c_1911])).
% 6.26/2.20  tff(c_1928, plain, (![A_587]: (k2_partfun1(k4_subset_1(A_587, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_587, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_587, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_587, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_587, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_587)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_587)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_587))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_564, c_1918])).
% 6.26/2.20  tff(c_1983, plain, (![A_592]: (k2_partfun1(k4_subset_1(A_592, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_592, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_592, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_592, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_592, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_592)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_592)) | v1_xboole_0(A_592))), inference(negUnitSimplification, [status(thm)], [c_64, c_1928])).
% 6.26/2.20  tff(c_666, plain, (![B_301, C_299, E_302, D_300, F_298, A_297]: (v1_funct_1(k1_tmap_1(A_297, B_301, C_299, D_300, E_302, F_298)) | ~m1_subset_1(F_298, k1_zfmisc_1(k2_zfmisc_1(D_300, B_301))) | ~v1_funct_2(F_298, D_300, B_301) | ~v1_funct_1(F_298) | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(C_299, B_301))) | ~v1_funct_2(E_302, C_299, B_301) | ~v1_funct_1(E_302) | ~m1_subset_1(D_300, k1_zfmisc_1(A_297)) | v1_xboole_0(D_300) | ~m1_subset_1(C_299, k1_zfmisc_1(A_297)) | v1_xboole_0(C_299) | v1_xboole_0(B_301) | v1_xboole_0(A_297))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.26/2.20  tff(c_668, plain, (![A_297, C_299, E_302]: (v1_funct_1(k1_tmap_1(A_297, '#skF_2', C_299, '#skF_4', E_302, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(C_299, '#skF_2'))) | ~v1_funct_2(E_302, C_299, '#skF_2') | ~v1_funct_1(E_302) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_297)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_299, k1_zfmisc_1(A_297)) | v1_xboole_0(C_299) | v1_xboole_0('#skF_2') | v1_xboole_0(A_297))), inference(resolution, [status(thm)], [c_44, c_666])).
% 6.26/2.20  tff(c_673, plain, (![A_297, C_299, E_302]: (v1_funct_1(k1_tmap_1(A_297, '#skF_2', C_299, '#skF_4', E_302, '#skF_6')) | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(C_299, '#skF_2'))) | ~v1_funct_2(E_302, C_299, '#skF_2') | ~v1_funct_1(E_302) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_297)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_299, k1_zfmisc_1(A_297)) | v1_xboole_0(C_299) | v1_xboole_0('#skF_2') | v1_xboole_0(A_297))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_668])).
% 6.26/2.20  tff(c_679, plain, (![A_303, C_304, E_305]: (v1_funct_1(k1_tmap_1(A_303, '#skF_2', C_304, '#skF_4', E_305, '#skF_6')) | ~m1_subset_1(E_305, k1_zfmisc_1(k2_zfmisc_1(C_304, '#skF_2'))) | ~v1_funct_2(E_305, C_304, '#skF_2') | ~v1_funct_1(E_305) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_303)) | ~m1_subset_1(C_304, k1_zfmisc_1(A_303)) | v1_xboole_0(C_304) | v1_xboole_0(A_303))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_673])).
% 6.26/2.20  tff(c_683, plain, (![A_303]: (v1_funct_1(k1_tmap_1(A_303, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_303)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_303)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_303))), inference(resolution, [status(thm)], [c_50, c_679])).
% 6.26/2.20  tff(c_690, plain, (![A_303]: (v1_funct_1(k1_tmap_1(A_303, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_303)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_303)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_303))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_683])).
% 6.26/2.20  tff(c_699, plain, (![A_307]: (v1_funct_1(k1_tmap_1(A_307, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_307)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_307)) | v1_xboole_0(A_307))), inference(negUnitSimplification, [status(thm)], [c_64, c_690])).
% 6.26/2.20  tff(c_702, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_699])).
% 6.26/2.20  tff(c_705, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_702])).
% 6.26/2.20  tff(c_706, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_68, c_705])).
% 6.26/2.20  tff(c_836, plain, (![E_339, C_338, F_336, D_340, B_337, A_335]: (k2_partfun1(k4_subset_1(A_335, C_338, D_340), B_337, k1_tmap_1(A_335, B_337, C_338, D_340, E_339, F_336), D_340)=F_336 | ~m1_subset_1(k1_tmap_1(A_335, B_337, C_338, D_340, E_339, F_336), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_335, C_338, D_340), B_337))) | ~v1_funct_2(k1_tmap_1(A_335, B_337, C_338, D_340, E_339, F_336), k4_subset_1(A_335, C_338, D_340), B_337) | ~v1_funct_1(k1_tmap_1(A_335, B_337, C_338, D_340, E_339, F_336)) | k2_partfun1(D_340, B_337, F_336, k9_subset_1(A_335, C_338, D_340))!=k2_partfun1(C_338, B_337, E_339, k9_subset_1(A_335, C_338, D_340)) | ~m1_subset_1(F_336, k1_zfmisc_1(k2_zfmisc_1(D_340, B_337))) | ~v1_funct_2(F_336, D_340, B_337) | ~v1_funct_1(F_336) | ~m1_subset_1(E_339, k1_zfmisc_1(k2_zfmisc_1(C_338, B_337))) | ~v1_funct_2(E_339, C_338, B_337) | ~v1_funct_1(E_339) | ~m1_subset_1(D_340, k1_zfmisc_1(A_335)) | v1_xboole_0(D_340) | ~m1_subset_1(C_338, k1_zfmisc_1(A_335)) | v1_xboole_0(C_338) | v1_xboole_0(B_337) | v1_xboole_0(A_335))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.26/2.20  tff(c_1167, plain, (![D_426, F_424, C_425, B_427, A_423, E_428]: (k2_partfun1(k4_subset_1(A_423, C_425, D_426), B_427, k1_tmap_1(A_423, B_427, C_425, D_426, E_428, F_424), D_426)=F_424 | ~v1_funct_2(k1_tmap_1(A_423, B_427, C_425, D_426, E_428, F_424), k4_subset_1(A_423, C_425, D_426), B_427) | ~v1_funct_1(k1_tmap_1(A_423, B_427, C_425, D_426, E_428, F_424)) | k2_partfun1(D_426, B_427, F_424, k9_subset_1(A_423, C_425, D_426))!=k2_partfun1(C_425, B_427, E_428, k9_subset_1(A_423, C_425, D_426)) | ~m1_subset_1(F_424, k1_zfmisc_1(k2_zfmisc_1(D_426, B_427))) | ~v1_funct_2(F_424, D_426, B_427) | ~v1_funct_1(F_424) | ~m1_subset_1(E_428, k1_zfmisc_1(k2_zfmisc_1(C_425, B_427))) | ~v1_funct_2(E_428, C_425, B_427) | ~v1_funct_1(E_428) | ~m1_subset_1(D_426, k1_zfmisc_1(A_423)) | v1_xboole_0(D_426) | ~m1_subset_1(C_425, k1_zfmisc_1(A_423)) | v1_xboole_0(C_425) | v1_xboole_0(B_427) | v1_xboole_0(A_423))), inference(resolution, [status(thm)], [c_36, c_836])).
% 6.26/2.20  tff(c_1339, plain, (![B_451, F_448, E_452, A_447, D_450, C_449]: (k2_partfun1(k4_subset_1(A_447, C_449, D_450), B_451, k1_tmap_1(A_447, B_451, C_449, D_450, E_452, F_448), D_450)=F_448 | ~v1_funct_1(k1_tmap_1(A_447, B_451, C_449, D_450, E_452, F_448)) | k2_partfun1(D_450, B_451, F_448, k9_subset_1(A_447, C_449, D_450))!=k2_partfun1(C_449, B_451, E_452, k9_subset_1(A_447, C_449, D_450)) | ~m1_subset_1(F_448, k1_zfmisc_1(k2_zfmisc_1(D_450, B_451))) | ~v1_funct_2(F_448, D_450, B_451) | ~v1_funct_1(F_448) | ~m1_subset_1(E_452, k1_zfmisc_1(k2_zfmisc_1(C_449, B_451))) | ~v1_funct_2(E_452, C_449, B_451) | ~v1_funct_1(E_452) | ~m1_subset_1(D_450, k1_zfmisc_1(A_447)) | v1_xboole_0(D_450) | ~m1_subset_1(C_449, k1_zfmisc_1(A_447)) | v1_xboole_0(C_449) | v1_xboole_0(B_451) | v1_xboole_0(A_447))), inference(resolution, [status(thm)], [c_38, c_1167])).
% 6.26/2.20  tff(c_1343, plain, (![A_447, C_449, E_452]: (k2_partfun1(k4_subset_1(A_447, C_449, '#skF_4'), '#skF_2', k1_tmap_1(A_447, '#skF_2', C_449, '#skF_4', E_452, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_447, '#skF_2', C_449, '#skF_4', E_452, '#skF_6')) | k2_partfun1(C_449, '#skF_2', E_452, k9_subset_1(A_447, C_449, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_447, C_449, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_452, k1_zfmisc_1(k2_zfmisc_1(C_449, '#skF_2'))) | ~v1_funct_2(E_452, C_449, '#skF_2') | ~v1_funct_1(E_452) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_447)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_449, k1_zfmisc_1(A_447)) | v1_xboole_0(C_449) | v1_xboole_0('#skF_2') | v1_xboole_0(A_447))), inference(resolution, [status(thm)], [c_44, c_1339])).
% 6.26/2.20  tff(c_1349, plain, (![A_447, C_449, E_452]: (k2_partfun1(k4_subset_1(A_447, C_449, '#skF_4'), '#skF_2', k1_tmap_1(A_447, '#skF_2', C_449, '#skF_4', E_452, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_447, '#skF_2', C_449, '#skF_4', E_452, '#skF_6')) | k2_partfun1(C_449, '#skF_2', E_452, k9_subset_1(A_447, C_449, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_447, C_449, '#skF_4')) | ~m1_subset_1(E_452, k1_zfmisc_1(k2_zfmisc_1(C_449, '#skF_2'))) | ~v1_funct_2(E_452, C_449, '#skF_2') | ~v1_funct_1(E_452) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_447)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_449, k1_zfmisc_1(A_447)) | v1_xboole_0(C_449) | v1_xboole_0('#skF_2') | v1_xboole_0(A_447))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_561, c_1343])).
% 6.26/2.20  tff(c_1355, plain, (![A_453, C_454, E_455]: (k2_partfun1(k4_subset_1(A_453, C_454, '#skF_4'), '#skF_2', k1_tmap_1(A_453, '#skF_2', C_454, '#skF_4', E_455, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_453, '#skF_2', C_454, '#skF_4', E_455, '#skF_6')) | k2_partfun1(C_454, '#skF_2', E_455, k9_subset_1(A_453, C_454, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_453, C_454, '#skF_4')) | ~m1_subset_1(E_455, k1_zfmisc_1(k2_zfmisc_1(C_454, '#skF_2'))) | ~v1_funct_2(E_455, C_454, '#skF_2') | ~v1_funct_1(E_455) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_453)) | ~m1_subset_1(C_454, k1_zfmisc_1(A_453)) | v1_xboole_0(C_454) | v1_xboole_0(A_453))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_1349])).
% 6.26/2.20  tff(c_1362, plain, (![A_453]: (k2_partfun1(k4_subset_1(A_453, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_453, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_453, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_453, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_453, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_453)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_453)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_453))), inference(resolution, [status(thm)], [c_50, c_1355])).
% 6.26/2.20  tff(c_1372, plain, (![A_453]: (k2_partfun1(k4_subset_1(A_453, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_453, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_453, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_453, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_453, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_453)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_453)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_453))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_564, c_1362])).
% 6.26/2.20  tff(c_1379, plain, (![A_465]: (k2_partfun1(k4_subset_1(A_465, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_465, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_465, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_465, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_465, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_465)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_465)) | v1_xboole_0(A_465))), inference(negUnitSimplification, [status(thm)], [c_64, c_1372])).
% 6.26/2.20  tff(c_100, plain, (![C_224, A_225, B_226]: (v1_relat_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.26/2.20  tff(c_107, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_100])).
% 6.26/2.20  tff(c_131, plain, (![A_231, B_232]: (v1_xboole_0(k7_relat_1(A_231, B_232)) | ~v1_xboole_0(B_232) | ~v1_relat_1(A_231))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.26/2.20  tff(c_136, plain, (![A_233, B_234]: (k7_relat_1(A_233, B_234)=k1_xboole_0 | ~v1_xboole_0(B_234) | ~v1_relat_1(A_233))), inference(resolution, [status(thm)], [c_131, c_8])).
% 6.26/2.20  tff(c_143, plain, (![A_235]: (k7_relat_1(A_235, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_235))), inference(resolution, [status(thm)], [c_6, c_136])).
% 6.26/2.20  tff(c_155, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_107, c_143])).
% 6.26/2.20  tff(c_108, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_100])).
% 6.26/2.20  tff(c_154, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_108, c_143])).
% 6.26/2.20  tff(c_174, plain, (![A_236, B_237]: (r1_xboole_0(A_236, B_237) | ~r1_subset_1(A_236, B_237) | v1_xboole_0(B_237) | v1_xboole_0(A_236))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.26/2.20  tff(c_341, plain, (![A_257, B_258]: (k3_xboole_0(A_257, B_258)=k1_xboole_0 | ~r1_subset_1(A_257, B_258) | v1_xboole_0(B_258) | v1_xboole_0(A_257))), inference(resolution, [status(thm)], [c_174, c_2])).
% 6.26/2.20  tff(c_347, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_341])).
% 6.26/2.20  tff(c_351, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_60, c_347])).
% 6.26/2.20  tff(c_310, plain, (![A_249, B_250, C_251, D_252]: (k2_partfun1(A_249, B_250, C_251, D_252)=k7_relat_1(C_251, D_252) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))) | ~v1_funct_1(C_251))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.26/2.20  tff(c_314, plain, (![D_252]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_252)=k7_relat_1('#skF_5', D_252) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_310])).
% 6.26/2.20  tff(c_320, plain, (![D_252]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_252)=k7_relat_1('#skF_5', D_252))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_314])).
% 6.26/2.20  tff(c_312, plain, (![D_252]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_252)=k7_relat_1('#skF_6', D_252) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_310])).
% 6.26/2.20  tff(c_317, plain, (![D_252]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_252)=k7_relat_1('#skF_6', D_252))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_312])).
% 6.26/2.20  tff(c_216, plain, (![A_240, B_241, C_242]: (k9_subset_1(A_240, B_241, C_242)=k3_xboole_0(B_241, C_242) | ~m1_subset_1(C_242, k1_zfmisc_1(A_240)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.26/2.20  tff(c_228, plain, (![B_241]: (k9_subset_1('#skF_1', B_241, '#skF_4')=k3_xboole_0(B_241, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_216])).
% 6.26/2.20  tff(c_42, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.26/2.20  tff(c_99, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_42])).
% 6.26/2.20  tff(c_238, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_228, c_99])).
% 6.26/2.20  tff(c_340, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_317, c_238])).
% 6.26/2.20  tff(c_352, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_351, c_351, c_340])).
% 6.26/2.20  tff(c_355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_154, c_352])).
% 6.26/2.20  tff(c_356, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_42])).
% 6.26/2.20  tff(c_665, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_356])).
% 6.26/2.20  tff(c_1390, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1379, c_665])).
% 6.26/2.20  tff(c_1404, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_413, c_607, c_412, c_607, c_534, c_534, c_706, c_1390])).
% 6.26/2.20  tff(c_1406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1404])).
% 6.26/2.20  tff(c_1407, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_356])).
% 6.26/2.20  tff(c_1992, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1983, c_1407])).
% 6.26/2.20  tff(c_2003, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_412, c_413, c_607, c_534, c_607, c_534, c_1453, c_1992])).
% 6.26/2.20  tff(c_2005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2003])).
% 6.26/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.26/2.20  
% 6.26/2.20  Inference rules
% 6.26/2.20  ----------------------
% 6.26/2.20  #Ref     : 0
% 6.26/2.20  #Sup     : 403
% 6.26/2.20  #Fact    : 0
% 6.26/2.20  #Define  : 0
% 6.26/2.20  #Split   : 7
% 6.26/2.20  #Chain   : 0
% 6.26/2.20  #Close   : 0
% 6.26/2.20  
% 6.26/2.20  Ordering : KBO
% 6.26/2.20  
% 6.26/2.20  Simplification rules
% 6.26/2.20  ----------------------
% 6.26/2.20  #Subsume      : 51
% 6.26/2.20  #Demod        : 409
% 6.26/2.20  #Tautology    : 169
% 6.26/2.20  #SimpNegUnit  : 112
% 6.26/2.20  #BackRed      : 3
% 6.26/2.20  
% 6.26/2.20  #Partial instantiations: 0
% 6.26/2.20  #Strategies tried      : 1
% 6.26/2.20  
% 6.26/2.20  Timing (in seconds)
% 6.26/2.20  ----------------------
% 6.26/2.20  Preprocessing        : 0.44
% 6.26/2.20  Parsing              : 0.21
% 6.26/2.20  CNF conversion       : 0.07
% 6.26/2.20  Main loop            : 0.96
% 6.26/2.20  Inferencing          : 0.35
% 6.26/2.20  Reduction            : 0.30
% 6.26/2.20  Demodulation         : 0.21
% 6.26/2.20  BG Simplification    : 0.04
% 6.26/2.20  Subsumption          : 0.21
% 6.26/2.20  Abstraction          : 0.05
% 6.26/2.20  MUC search           : 0.00
% 6.26/2.20  Cooper               : 0.00
% 6.26/2.20  Total                : 1.45
% 6.26/2.20  Index Insertion      : 0.00
% 6.26/2.21  Index Deletion       : 0.00
% 6.26/2.21  Index Matching       : 0.00
% 6.26/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
