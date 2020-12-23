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
% DateTime   : Thu Dec  3 10:26:15 EST 2020

% Result     : Theorem 5.62s
% Output     : CNFRefutation 5.98s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 435 expanded)
%              Number of leaves         :   39 ( 177 expanded)
%              Depth                    :   12
%              Number of atoms          :  578 (2482 expanded)
%              Number of equality atoms :  100 ( 446 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_389,plain,(
    ! [C_265,A_266,B_267] :
      ( v1_relat_1(C_265)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_396,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_389])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_379,plain,(
    ! [A_263,B_264] :
      ( v1_xboole_0(k7_relat_1(A_263,B_264))
      | ~ v1_xboole_0(B_264)
      | ~ v1_relat_1(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_398,plain,(
    ! [A_268,B_269] :
      ( k7_relat_1(A_268,B_269) = k1_xboole_0
      | ~ v1_xboole_0(B_269)
      | ~ v1_relat_1(A_268) ) ),
    inference(resolution,[status(thm)],[c_379,c_8])).

tff(c_405,plain,(
    ! [A_270] :
      ( k7_relat_1(A_270,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_270) ) ),
    inference(resolution,[status(thm)],[c_6,c_398])).

tff(c_416,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_396,c_405])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_56,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_418,plain,(
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

tff(c_1367,plain,(
    ! [A_435,B_436] :
      ( k3_xboole_0(A_435,B_436) = k1_xboole_0
      | ~ r1_subset_1(A_435,B_436)
      | v1_xboole_0(B_436)
      | v1_xboole_0(A_435) ) ),
    inference(resolution,[status(thm)],[c_418,c_2])).

tff(c_1370,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1367])).

tff(c_1373,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_60,c_1370])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_397,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_389])).

tff(c_415,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_397,c_405])).

tff(c_1313,plain,(
    ! [A_428,B_429,C_430] :
      ( k9_subset_1(A_428,B_429,C_430) = k3_xboole_0(B_429,C_430)
      | ~ m1_subset_1(C_430,k1_zfmisc_1(A_428)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1325,plain,(
    ! [B_429] : k9_subset_1('#skF_1',B_429,'#skF_4') = k3_xboole_0(B_429,'#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1313])).

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

tff(c_1482,plain,(
    ! [F_449,C_450,A_448,E_453,D_451,B_452] :
      ( v1_funct_1(k1_tmap_1(A_448,B_452,C_450,D_451,E_453,F_449))
      | ~ m1_subset_1(F_449,k1_zfmisc_1(k2_zfmisc_1(D_451,B_452)))
      | ~ v1_funct_2(F_449,D_451,B_452)
      | ~ v1_funct_1(F_449)
      | ~ m1_subset_1(E_453,k1_zfmisc_1(k2_zfmisc_1(C_450,B_452)))
      | ~ v1_funct_2(E_453,C_450,B_452)
      | ~ v1_funct_1(E_453)
      | ~ m1_subset_1(D_451,k1_zfmisc_1(A_448))
      | v1_xboole_0(D_451)
      | ~ m1_subset_1(C_450,k1_zfmisc_1(A_448))
      | v1_xboole_0(C_450)
      | v1_xboole_0(B_452)
      | v1_xboole_0(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1484,plain,(
    ! [A_448,C_450,E_453] :
      ( v1_funct_1(k1_tmap_1(A_448,'#skF_2',C_450,'#skF_4',E_453,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_453,k1_zfmisc_1(k2_zfmisc_1(C_450,'#skF_2')))
      | ~ v1_funct_2(E_453,C_450,'#skF_2')
      | ~ v1_funct_1(E_453)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_448))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_450,k1_zfmisc_1(A_448))
      | v1_xboole_0(C_450)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_448) ) ),
    inference(resolution,[status(thm)],[c_44,c_1482])).

tff(c_1489,plain,(
    ! [A_448,C_450,E_453] :
      ( v1_funct_1(k1_tmap_1(A_448,'#skF_2',C_450,'#skF_4',E_453,'#skF_6'))
      | ~ m1_subset_1(E_453,k1_zfmisc_1(k2_zfmisc_1(C_450,'#skF_2')))
      | ~ v1_funct_2(E_453,C_450,'#skF_2')
      | ~ v1_funct_1(E_453)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_448))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_450,k1_zfmisc_1(A_448))
      | v1_xboole_0(C_450)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_448) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1484])).

tff(c_1495,plain,(
    ! [A_454,C_455,E_456] :
      ( v1_funct_1(k1_tmap_1(A_454,'#skF_2',C_455,'#skF_4',E_456,'#skF_6'))
      | ~ m1_subset_1(E_456,k1_zfmisc_1(k2_zfmisc_1(C_455,'#skF_2')))
      | ~ v1_funct_2(E_456,C_455,'#skF_2')
      | ~ v1_funct_1(E_456)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_454))
      | ~ m1_subset_1(C_455,k1_zfmisc_1(A_454))
      | v1_xboole_0(C_455)
      | v1_xboole_0(A_454) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_1489])).

tff(c_1499,plain,(
    ! [A_454] :
      ( v1_funct_1(k1_tmap_1(A_454,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_454))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_454))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_454) ) ),
    inference(resolution,[status(thm)],[c_50,c_1495])).

tff(c_1506,plain,(
    ! [A_454] :
      ( v1_funct_1(k1_tmap_1(A_454,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_454))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_454))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_454) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1499])).

tff(c_1515,plain,(
    ! [A_458] :
      ( v1_funct_1(k1_tmap_1(A_458,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_458))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_458))
      | v1_xboole_0(A_458) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1506])).

tff(c_1518,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_1515])).

tff(c_1521,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1518])).

tff(c_1522,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1521])).

tff(c_1439,plain,(
    ! [A_442,B_443,C_444,D_445] :
      ( k2_partfun1(A_442,B_443,C_444,D_445) = k7_relat_1(C_444,D_445)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_442,B_443)))
      | ~ v1_funct_1(C_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1443,plain,(
    ! [D_445] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_445) = k7_relat_1('#skF_5',D_445)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_1439])).

tff(c_1449,plain,(
    ! [D_445] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_445) = k7_relat_1('#skF_5',D_445) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1443])).

tff(c_1441,plain,(
    ! [D_445] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_445) = k7_relat_1('#skF_6',D_445)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_44,c_1439])).

tff(c_1446,plain,(
    ! [D_445] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_445) = k7_relat_1('#skF_6',D_445) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1441])).

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

tff(c_1617,plain,(
    ! [F_486,D_490,C_488,A_485,E_489,B_487] :
      ( k2_partfun1(k4_subset_1(A_485,C_488,D_490),B_487,k1_tmap_1(A_485,B_487,C_488,D_490,E_489,F_486),C_488) = E_489
      | ~ m1_subset_1(k1_tmap_1(A_485,B_487,C_488,D_490,E_489,F_486),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_485,C_488,D_490),B_487)))
      | ~ v1_funct_2(k1_tmap_1(A_485,B_487,C_488,D_490,E_489,F_486),k4_subset_1(A_485,C_488,D_490),B_487)
      | ~ v1_funct_1(k1_tmap_1(A_485,B_487,C_488,D_490,E_489,F_486))
      | k2_partfun1(D_490,B_487,F_486,k9_subset_1(A_485,C_488,D_490)) != k2_partfun1(C_488,B_487,E_489,k9_subset_1(A_485,C_488,D_490))
      | ~ m1_subset_1(F_486,k1_zfmisc_1(k2_zfmisc_1(D_490,B_487)))
      | ~ v1_funct_2(F_486,D_490,B_487)
      | ~ v1_funct_1(F_486)
      | ~ m1_subset_1(E_489,k1_zfmisc_1(k2_zfmisc_1(C_488,B_487)))
      | ~ v1_funct_2(E_489,C_488,B_487)
      | ~ v1_funct_1(E_489)
      | ~ m1_subset_1(D_490,k1_zfmisc_1(A_485))
      | v1_xboole_0(D_490)
      | ~ m1_subset_1(C_488,k1_zfmisc_1(A_485))
      | v1_xboole_0(C_488)
      | v1_xboole_0(B_487)
      | v1_xboole_0(A_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1956,plain,(
    ! [D_554,A_551,E_556,C_553,B_555,F_552] :
      ( k2_partfun1(k4_subset_1(A_551,C_553,D_554),B_555,k1_tmap_1(A_551,B_555,C_553,D_554,E_556,F_552),C_553) = E_556
      | ~ v1_funct_2(k1_tmap_1(A_551,B_555,C_553,D_554,E_556,F_552),k4_subset_1(A_551,C_553,D_554),B_555)
      | ~ v1_funct_1(k1_tmap_1(A_551,B_555,C_553,D_554,E_556,F_552))
      | k2_partfun1(D_554,B_555,F_552,k9_subset_1(A_551,C_553,D_554)) != k2_partfun1(C_553,B_555,E_556,k9_subset_1(A_551,C_553,D_554))
      | ~ m1_subset_1(F_552,k1_zfmisc_1(k2_zfmisc_1(D_554,B_555)))
      | ~ v1_funct_2(F_552,D_554,B_555)
      | ~ v1_funct_1(F_552)
      | ~ m1_subset_1(E_556,k1_zfmisc_1(k2_zfmisc_1(C_553,B_555)))
      | ~ v1_funct_2(E_556,C_553,B_555)
      | ~ v1_funct_1(E_556)
      | ~ m1_subset_1(D_554,k1_zfmisc_1(A_551))
      | v1_xboole_0(D_554)
      | ~ m1_subset_1(C_553,k1_zfmisc_1(A_551))
      | v1_xboole_0(C_553)
      | v1_xboole_0(B_555)
      | v1_xboole_0(A_551) ) ),
    inference(resolution,[status(thm)],[c_36,c_1617])).

tff(c_1964,plain,(
    ! [F_564,A_563,C_565,B_567,E_568,D_566] :
      ( k2_partfun1(k4_subset_1(A_563,C_565,D_566),B_567,k1_tmap_1(A_563,B_567,C_565,D_566,E_568,F_564),C_565) = E_568
      | ~ v1_funct_1(k1_tmap_1(A_563,B_567,C_565,D_566,E_568,F_564))
      | k2_partfun1(D_566,B_567,F_564,k9_subset_1(A_563,C_565,D_566)) != k2_partfun1(C_565,B_567,E_568,k9_subset_1(A_563,C_565,D_566))
      | ~ m1_subset_1(F_564,k1_zfmisc_1(k2_zfmisc_1(D_566,B_567)))
      | ~ v1_funct_2(F_564,D_566,B_567)
      | ~ v1_funct_1(F_564)
      | ~ m1_subset_1(E_568,k1_zfmisc_1(k2_zfmisc_1(C_565,B_567)))
      | ~ v1_funct_2(E_568,C_565,B_567)
      | ~ v1_funct_1(E_568)
      | ~ m1_subset_1(D_566,k1_zfmisc_1(A_563))
      | v1_xboole_0(D_566)
      | ~ m1_subset_1(C_565,k1_zfmisc_1(A_563))
      | v1_xboole_0(C_565)
      | v1_xboole_0(B_567)
      | v1_xboole_0(A_563) ) ),
    inference(resolution,[status(thm)],[c_38,c_1956])).

tff(c_1968,plain,(
    ! [A_563,C_565,E_568] :
      ( k2_partfun1(k4_subset_1(A_563,C_565,'#skF_4'),'#skF_2',k1_tmap_1(A_563,'#skF_2',C_565,'#skF_4',E_568,'#skF_6'),C_565) = E_568
      | ~ v1_funct_1(k1_tmap_1(A_563,'#skF_2',C_565,'#skF_4',E_568,'#skF_6'))
      | k2_partfun1(C_565,'#skF_2',E_568,k9_subset_1(A_563,C_565,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_563,C_565,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_568,k1_zfmisc_1(k2_zfmisc_1(C_565,'#skF_2')))
      | ~ v1_funct_2(E_568,C_565,'#skF_2')
      | ~ v1_funct_1(E_568)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_563))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_565,k1_zfmisc_1(A_563))
      | v1_xboole_0(C_565)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_563) ) ),
    inference(resolution,[status(thm)],[c_44,c_1964])).

tff(c_1974,plain,(
    ! [A_563,C_565,E_568] :
      ( k2_partfun1(k4_subset_1(A_563,C_565,'#skF_4'),'#skF_2',k1_tmap_1(A_563,'#skF_2',C_565,'#skF_4',E_568,'#skF_6'),C_565) = E_568
      | ~ v1_funct_1(k1_tmap_1(A_563,'#skF_2',C_565,'#skF_4',E_568,'#skF_6'))
      | k2_partfun1(C_565,'#skF_2',E_568,k9_subset_1(A_563,C_565,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_563,C_565,'#skF_4'))
      | ~ m1_subset_1(E_568,k1_zfmisc_1(k2_zfmisc_1(C_565,'#skF_2')))
      | ~ v1_funct_2(E_568,C_565,'#skF_2')
      | ~ v1_funct_1(E_568)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_563))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_565,k1_zfmisc_1(A_563))
      | v1_xboole_0(C_565)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_563) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1446,c_1968])).

tff(c_1980,plain,(
    ! [A_569,C_570,E_571] :
      ( k2_partfun1(k4_subset_1(A_569,C_570,'#skF_4'),'#skF_2',k1_tmap_1(A_569,'#skF_2',C_570,'#skF_4',E_571,'#skF_6'),C_570) = E_571
      | ~ v1_funct_1(k1_tmap_1(A_569,'#skF_2',C_570,'#skF_4',E_571,'#skF_6'))
      | k2_partfun1(C_570,'#skF_2',E_571,k9_subset_1(A_569,C_570,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_569,C_570,'#skF_4'))
      | ~ m1_subset_1(E_571,k1_zfmisc_1(k2_zfmisc_1(C_570,'#skF_2')))
      | ~ v1_funct_2(E_571,C_570,'#skF_2')
      | ~ v1_funct_1(E_571)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_569))
      | ~ m1_subset_1(C_570,k1_zfmisc_1(A_569))
      | v1_xboole_0(C_570)
      | v1_xboole_0(A_569) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_1974])).

tff(c_1987,plain,(
    ! [A_569] :
      ( k2_partfun1(k4_subset_1(A_569,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_569,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_569,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_569,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_569,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_569))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_569))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_569) ) ),
    inference(resolution,[status(thm)],[c_50,c_1980])).

tff(c_1997,plain,(
    ! [A_569] :
      ( k2_partfun1(k4_subset_1(A_569,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_569,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_569,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_569,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_569,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_569))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_569))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_569) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1449,c_1987])).

tff(c_2021,plain,(
    ! [A_573] :
      ( k2_partfun1(k4_subset_1(A_573,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_573,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_573,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_573,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_573,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_573))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_573))
      | v1_xboole_0(A_573) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1997])).

tff(c_577,plain,(
    ! [A_284,B_285] :
      ( k3_xboole_0(A_284,B_285) = k1_xboole_0
      | ~ r1_subset_1(A_284,B_285)
      | v1_xboole_0(B_285)
      | v1_xboole_0(A_284) ) ),
    inference(resolution,[status(thm)],[c_418,c_2])).

tff(c_580,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_577])).

tff(c_583,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_60,c_580])).

tff(c_523,plain,(
    ! [A_277,B_278,C_279] :
      ( k9_subset_1(A_277,B_278,C_279) = k3_xboole_0(B_278,C_279)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(A_277)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_535,plain,(
    ! [B_278] : k9_subset_1('#skF_1',B_278,'#skF_4') = k3_xboole_0(B_278,'#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_523])).

tff(c_688,plain,(
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

tff(c_690,plain,(
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
    inference(resolution,[status(thm)],[c_44,c_688])).

tff(c_695,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_690])).

tff(c_701,plain,(
    ! [A_303,C_304,E_305] :
      ( v1_funct_1(k1_tmap_1(A_303,'#skF_2',C_304,'#skF_4',E_305,'#skF_6'))
      | ~ m1_subset_1(E_305,k1_zfmisc_1(k2_zfmisc_1(C_304,'#skF_2')))
      | ~ v1_funct_2(E_305,C_304,'#skF_2')
      | ~ v1_funct_1(E_305)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_303))
      | ~ m1_subset_1(C_304,k1_zfmisc_1(A_303))
      | v1_xboole_0(C_304)
      | v1_xboole_0(A_303) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_695])).

tff(c_705,plain,(
    ! [A_303] :
      ( v1_funct_1(k1_tmap_1(A_303,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_303))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_303))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_303) ) ),
    inference(resolution,[status(thm)],[c_50,c_701])).

tff(c_712,plain,(
    ! [A_303] :
      ( v1_funct_1(k1_tmap_1(A_303,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_303))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_303))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_705])).

tff(c_721,plain,(
    ! [A_307] :
      ( v1_funct_1(k1_tmap_1(A_307,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_307))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_307))
      | v1_xboole_0(A_307) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_712])).

tff(c_724,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_721])).

tff(c_727,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_724])).

tff(c_728,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_727])).

tff(c_645,plain,(
    ! [A_291,B_292,C_293,D_294] :
      ( k2_partfun1(A_291,B_292,C_293,D_294) = k7_relat_1(C_293,D_294)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292)))
      | ~ v1_funct_1(C_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_649,plain,(
    ! [D_294] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_294) = k7_relat_1('#skF_5',D_294)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_645])).

tff(c_655,plain,(
    ! [D_294] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_294) = k7_relat_1('#skF_5',D_294) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_649])).

tff(c_647,plain,(
    ! [D_294] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_294) = k7_relat_1('#skF_6',D_294)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_44,c_645])).

tff(c_652,plain,(
    ! [D_294] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_294) = k7_relat_1('#skF_6',D_294) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_647])).

tff(c_952,plain,(
    ! [C_349,F_347,D_351,A_346,B_348,E_350] :
      ( k2_partfun1(k4_subset_1(A_346,C_349,D_351),B_348,k1_tmap_1(A_346,B_348,C_349,D_351,E_350,F_347),D_351) = F_347
      | ~ m1_subset_1(k1_tmap_1(A_346,B_348,C_349,D_351,E_350,F_347),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_346,C_349,D_351),B_348)))
      | ~ v1_funct_2(k1_tmap_1(A_346,B_348,C_349,D_351,E_350,F_347),k4_subset_1(A_346,C_349,D_351),B_348)
      | ~ v1_funct_1(k1_tmap_1(A_346,B_348,C_349,D_351,E_350,F_347))
      | k2_partfun1(D_351,B_348,F_347,k9_subset_1(A_346,C_349,D_351)) != k2_partfun1(C_349,B_348,E_350,k9_subset_1(A_346,C_349,D_351))
      | ~ m1_subset_1(F_347,k1_zfmisc_1(k2_zfmisc_1(D_351,B_348)))
      | ~ v1_funct_2(F_347,D_351,B_348)
      | ~ v1_funct_1(F_347)
      | ~ m1_subset_1(E_350,k1_zfmisc_1(k2_zfmisc_1(C_349,B_348)))
      | ~ v1_funct_2(E_350,C_349,B_348)
      | ~ v1_funct_1(E_350)
      | ~ m1_subset_1(D_351,k1_zfmisc_1(A_346))
      | v1_xboole_0(D_351)
      | ~ m1_subset_1(C_349,k1_zfmisc_1(A_346))
      | v1_xboole_0(C_349)
      | v1_xboole_0(B_348)
      | v1_xboole_0(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1120,plain,(
    ! [B_404,F_401,C_402,D_403,A_400,E_405] :
      ( k2_partfun1(k4_subset_1(A_400,C_402,D_403),B_404,k1_tmap_1(A_400,B_404,C_402,D_403,E_405,F_401),D_403) = F_401
      | ~ v1_funct_2(k1_tmap_1(A_400,B_404,C_402,D_403,E_405,F_401),k4_subset_1(A_400,C_402,D_403),B_404)
      | ~ v1_funct_1(k1_tmap_1(A_400,B_404,C_402,D_403,E_405,F_401))
      | k2_partfun1(D_403,B_404,F_401,k9_subset_1(A_400,C_402,D_403)) != k2_partfun1(C_402,B_404,E_405,k9_subset_1(A_400,C_402,D_403))
      | ~ m1_subset_1(F_401,k1_zfmisc_1(k2_zfmisc_1(D_403,B_404)))
      | ~ v1_funct_2(F_401,D_403,B_404)
      | ~ v1_funct_1(F_401)
      | ~ m1_subset_1(E_405,k1_zfmisc_1(k2_zfmisc_1(C_402,B_404)))
      | ~ v1_funct_2(E_405,C_402,B_404)
      | ~ v1_funct_1(E_405)
      | ~ m1_subset_1(D_403,k1_zfmisc_1(A_400))
      | v1_xboole_0(D_403)
      | ~ m1_subset_1(C_402,k1_zfmisc_1(A_400))
      | v1_xboole_0(C_402)
      | v1_xboole_0(B_404)
      | v1_xboole_0(A_400) ) ),
    inference(resolution,[status(thm)],[c_36,c_952])).

tff(c_1124,plain,(
    ! [D_409,C_408,F_407,B_410,E_411,A_406] :
      ( k2_partfun1(k4_subset_1(A_406,C_408,D_409),B_410,k1_tmap_1(A_406,B_410,C_408,D_409,E_411,F_407),D_409) = F_407
      | ~ v1_funct_1(k1_tmap_1(A_406,B_410,C_408,D_409,E_411,F_407))
      | k2_partfun1(D_409,B_410,F_407,k9_subset_1(A_406,C_408,D_409)) != k2_partfun1(C_408,B_410,E_411,k9_subset_1(A_406,C_408,D_409))
      | ~ m1_subset_1(F_407,k1_zfmisc_1(k2_zfmisc_1(D_409,B_410)))
      | ~ v1_funct_2(F_407,D_409,B_410)
      | ~ v1_funct_1(F_407)
      | ~ m1_subset_1(E_411,k1_zfmisc_1(k2_zfmisc_1(C_408,B_410)))
      | ~ v1_funct_2(E_411,C_408,B_410)
      | ~ v1_funct_1(E_411)
      | ~ m1_subset_1(D_409,k1_zfmisc_1(A_406))
      | v1_xboole_0(D_409)
      | ~ m1_subset_1(C_408,k1_zfmisc_1(A_406))
      | v1_xboole_0(C_408)
      | v1_xboole_0(B_410)
      | v1_xboole_0(A_406) ) ),
    inference(resolution,[status(thm)],[c_38,c_1120])).

tff(c_1128,plain,(
    ! [A_406,C_408,E_411] :
      ( k2_partfun1(k4_subset_1(A_406,C_408,'#skF_4'),'#skF_2',k1_tmap_1(A_406,'#skF_2',C_408,'#skF_4',E_411,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_406,'#skF_2',C_408,'#skF_4',E_411,'#skF_6'))
      | k2_partfun1(C_408,'#skF_2',E_411,k9_subset_1(A_406,C_408,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_406,C_408,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_411,k1_zfmisc_1(k2_zfmisc_1(C_408,'#skF_2')))
      | ~ v1_funct_2(E_411,C_408,'#skF_2')
      | ~ v1_funct_1(E_411)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_406))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_408,k1_zfmisc_1(A_406))
      | v1_xboole_0(C_408)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_406) ) ),
    inference(resolution,[status(thm)],[c_44,c_1124])).

tff(c_1134,plain,(
    ! [A_406,C_408,E_411] :
      ( k2_partfun1(k4_subset_1(A_406,C_408,'#skF_4'),'#skF_2',k1_tmap_1(A_406,'#skF_2',C_408,'#skF_4',E_411,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_406,'#skF_2',C_408,'#skF_4',E_411,'#skF_6'))
      | k2_partfun1(C_408,'#skF_2',E_411,k9_subset_1(A_406,C_408,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_406,C_408,'#skF_4'))
      | ~ m1_subset_1(E_411,k1_zfmisc_1(k2_zfmisc_1(C_408,'#skF_2')))
      | ~ v1_funct_2(E_411,C_408,'#skF_2')
      | ~ v1_funct_1(E_411)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_406))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_408,k1_zfmisc_1(A_406))
      | v1_xboole_0(C_408)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_406) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_652,c_1128])).

tff(c_1140,plain,(
    ! [A_412,C_413,E_414] :
      ( k2_partfun1(k4_subset_1(A_412,C_413,'#skF_4'),'#skF_2',k1_tmap_1(A_412,'#skF_2',C_413,'#skF_4',E_414,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_412,'#skF_2',C_413,'#skF_4',E_414,'#skF_6'))
      | k2_partfun1(C_413,'#skF_2',E_414,k9_subset_1(A_412,C_413,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_412,C_413,'#skF_4'))
      | ~ m1_subset_1(E_414,k1_zfmisc_1(k2_zfmisc_1(C_413,'#skF_2')))
      | ~ v1_funct_2(E_414,C_413,'#skF_2')
      | ~ v1_funct_1(E_414)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_412))
      | ~ m1_subset_1(C_413,k1_zfmisc_1(A_412))
      | v1_xboole_0(C_413)
      | v1_xboole_0(A_412) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_1134])).

tff(c_1147,plain,(
    ! [A_412] :
      ( k2_partfun1(k4_subset_1(A_412,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_412,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_412,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_412,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_412,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_412))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_412))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_412) ) ),
    inference(resolution,[status(thm)],[c_50,c_1140])).

tff(c_1157,plain,(
    ! [A_412] :
      ( k2_partfun1(k4_subset_1(A_412,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_412,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_412,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_412,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_412,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_412))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_412))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_412) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_655,c_1147])).

tff(c_1216,plain,(
    ! [A_423] :
      ( k2_partfun1(k4_subset_1(A_423,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_423,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_423,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_423,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_423,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_423))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_423))
      | v1_xboole_0(A_423) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1157])).

tff(c_127,plain,(
    ! [C_230,A_231,B_232] :
      ( v1_relat_1(C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_134,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_127])).

tff(c_122,plain,(
    ! [A_228,B_229] :
      ( v1_xboole_0(k7_relat_1(A_228,B_229))
      | ~ v1_xboole_0(B_229)
      | ~ v1_relat_1(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_136,plain,(
    ! [A_233,B_234] :
      ( k7_relat_1(A_233,B_234) = k1_xboole_0
      | ~ v1_xboole_0(B_234)
      | ~ v1_relat_1(A_233) ) ),
    inference(resolution,[status(thm)],[c_122,c_8])).

tff(c_143,plain,(
    ! [A_235] :
      ( k7_relat_1(A_235,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_235) ) ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_154,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_134,c_143])).

tff(c_135,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_127])).

tff(c_153,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_135,c_143])).

tff(c_188,plain,(
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
    inference(resolution,[status(thm)],[c_188,c_2])).

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

tff(c_260,plain,(
    ! [A_242,B_243,C_244] :
      ( k9_subset_1(A_242,B_243,C_244) = k3_xboole_0(B_243,C_244)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(A_242)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_272,plain,(
    ! [B_243] : k9_subset_1('#skF_1',B_243,'#skF_4') = k3_xboole_0(B_243,'#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_260])).

tff(c_42,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_99,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_282,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_272,c_99])).

tff(c_340,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_317,c_282])).

tff(c_352,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_351,c_340])).

tff(c_355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_153,c_352])).

tff(c_356,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_455,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_1227,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1216,c_455])).

tff(c_1241,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_416,c_583,c_415,c_583,c_535,c_535,c_728,c_1227])).

tff(c_1243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1241])).

tff(c_1244,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_2030,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2021,c_1244])).

tff(c_2041,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_416,c_1373,c_415,c_1373,c_1325,c_1325,c_1522,c_2030])).

tff(c_2043,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2041])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n001.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 11:42:44 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.62/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.62/2.07  
% 5.62/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.62/2.08  %$ v1_funct_2 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.62/2.08  
% 5.62/2.08  %Foreground sorts:
% 5.62/2.08  
% 5.62/2.08  
% 5.62/2.08  %Background operators:
% 5.62/2.08  
% 5.62/2.08  
% 5.62/2.08  %Foreground operators:
% 5.62/2.08  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 5.62/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.62/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.62/2.08  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.62/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.62/2.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.62/2.08  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.62/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.62/2.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.62/2.08  tff('#skF_6', type, '#skF_6': $i).
% 5.62/2.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.62/2.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.62/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.62/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.62/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.62/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.62/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.62/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.62/2.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.62/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.62/2.08  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.62/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.62/2.08  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.62/2.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.62/2.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.62/2.08  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.62/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.62/2.08  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.62/2.08  
% 5.98/2.10  tff(f_201, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 5.98/2.10  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.98/2.10  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.98/2.10  tff(f_57, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc16_relat_1)).
% 5.98/2.10  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.98/2.10  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 5.98/2.10  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.98/2.10  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.98/2.10  tff(f_159, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 5.98/2.10  tff(f_77, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 5.98/2.10  tff(f_125, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 5.98/2.10  tff(c_68, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.98/2.10  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.98/2.10  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.98/2.10  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.98/2.10  tff(c_389, plain, (![C_265, A_266, B_267]: (v1_relat_1(C_265) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_266, B_267))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.98/2.10  tff(c_396, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_389])).
% 5.98/2.10  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.98/2.10  tff(c_379, plain, (![A_263, B_264]: (v1_xboole_0(k7_relat_1(A_263, B_264)) | ~v1_xboole_0(B_264) | ~v1_relat_1(A_263))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.98/2.10  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.98/2.10  tff(c_398, plain, (![A_268, B_269]: (k7_relat_1(A_268, B_269)=k1_xboole_0 | ~v1_xboole_0(B_269) | ~v1_relat_1(A_268))), inference(resolution, [status(thm)], [c_379, c_8])).
% 5.98/2.10  tff(c_405, plain, (![A_270]: (k7_relat_1(A_270, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_270))), inference(resolution, [status(thm)], [c_6, c_398])).
% 5.98/2.10  tff(c_416, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_396, c_405])).
% 5.98/2.10  tff(c_64, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.98/2.10  tff(c_60, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.98/2.10  tff(c_56, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.98/2.10  tff(c_418, plain, (![A_271, B_272]: (r1_xboole_0(A_271, B_272) | ~r1_subset_1(A_271, B_272) | v1_xboole_0(B_272) | v1_xboole_0(A_271))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.98/2.10  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.98/2.10  tff(c_1367, plain, (![A_435, B_436]: (k3_xboole_0(A_435, B_436)=k1_xboole_0 | ~r1_subset_1(A_435, B_436) | v1_xboole_0(B_436) | v1_xboole_0(A_435))), inference(resolution, [status(thm)], [c_418, c_2])).
% 5.98/2.10  tff(c_1370, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1367])).
% 5.98/2.10  tff(c_1373, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_60, c_1370])).
% 5.98/2.10  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.98/2.10  tff(c_397, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_389])).
% 5.98/2.10  tff(c_415, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_397, c_405])).
% 5.98/2.10  tff(c_1313, plain, (![A_428, B_429, C_430]: (k9_subset_1(A_428, B_429, C_430)=k3_xboole_0(B_429, C_430) | ~m1_subset_1(C_430, k1_zfmisc_1(A_428)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.98/2.10  tff(c_1325, plain, (![B_429]: (k9_subset_1('#skF_1', B_429, '#skF_4')=k3_xboole_0(B_429, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_1313])).
% 5.98/2.10  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.98/2.10  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.98/2.10  tff(c_66, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.98/2.10  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.98/2.10  tff(c_46, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.98/2.10  tff(c_1482, plain, (![F_449, C_450, A_448, E_453, D_451, B_452]: (v1_funct_1(k1_tmap_1(A_448, B_452, C_450, D_451, E_453, F_449)) | ~m1_subset_1(F_449, k1_zfmisc_1(k2_zfmisc_1(D_451, B_452))) | ~v1_funct_2(F_449, D_451, B_452) | ~v1_funct_1(F_449) | ~m1_subset_1(E_453, k1_zfmisc_1(k2_zfmisc_1(C_450, B_452))) | ~v1_funct_2(E_453, C_450, B_452) | ~v1_funct_1(E_453) | ~m1_subset_1(D_451, k1_zfmisc_1(A_448)) | v1_xboole_0(D_451) | ~m1_subset_1(C_450, k1_zfmisc_1(A_448)) | v1_xboole_0(C_450) | v1_xboole_0(B_452) | v1_xboole_0(A_448))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.98/2.10  tff(c_1484, plain, (![A_448, C_450, E_453]: (v1_funct_1(k1_tmap_1(A_448, '#skF_2', C_450, '#skF_4', E_453, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_453, k1_zfmisc_1(k2_zfmisc_1(C_450, '#skF_2'))) | ~v1_funct_2(E_453, C_450, '#skF_2') | ~v1_funct_1(E_453) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_448)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_450, k1_zfmisc_1(A_448)) | v1_xboole_0(C_450) | v1_xboole_0('#skF_2') | v1_xboole_0(A_448))), inference(resolution, [status(thm)], [c_44, c_1482])).
% 5.98/2.10  tff(c_1489, plain, (![A_448, C_450, E_453]: (v1_funct_1(k1_tmap_1(A_448, '#skF_2', C_450, '#skF_4', E_453, '#skF_6')) | ~m1_subset_1(E_453, k1_zfmisc_1(k2_zfmisc_1(C_450, '#skF_2'))) | ~v1_funct_2(E_453, C_450, '#skF_2') | ~v1_funct_1(E_453) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_448)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_450, k1_zfmisc_1(A_448)) | v1_xboole_0(C_450) | v1_xboole_0('#skF_2') | v1_xboole_0(A_448))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1484])).
% 5.98/2.10  tff(c_1495, plain, (![A_454, C_455, E_456]: (v1_funct_1(k1_tmap_1(A_454, '#skF_2', C_455, '#skF_4', E_456, '#skF_6')) | ~m1_subset_1(E_456, k1_zfmisc_1(k2_zfmisc_1(C_455, '#skF_2'))) | ~v1_funct_2(E_456, C_455, '#skF_2') | ~v1_funct_1(E_456) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_454)) | ~m1_subset_1(C_455, k1_zfmisc_1(A_454)) | v1_xboole_0(C_455) | v1_xboole_0(A_454))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_1489])).
% 5.98/2.10  tff(c_1499, plain, (![A_454]: (v1_funct_1(k1_tmap_1(A_454, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_454)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_454)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_454))), inference(resolution, [status(thm)], [c_50, c_1495])).
% 5.98/2.10  tff(c_1506, plain, (![A_454]: (v1_funct_1(k1_tmap_1(A_454, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_454)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_454)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_454))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1499])).
% 5.98/2.10  tff(c_1515, plain, (![A_458]: (v1_funct_1(k1_tmap_1(A_458, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_458)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_458)) | v1_xboole_0(A_458))), inference(negUnitSimplification, [status(thm)], [c_64, c_1506])).
% 5.98/2.10  tff(c_1518, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_1515])).
% 5.98/2.10  tff(c_1521, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1518])).
% 5.98/2.10  tff(c_1522, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1521])).
% 5.98/2.10  tff(c_1439, plain, (![A_442, B_443, C_444, D_445]: (k2_partfun1(A_442, B_443, C_444, D_445)=k7_relat_1(C_444, D_445) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_442, B_443))) | ~v1_funct_1(C_444))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.98/2.10  tff(c_1443, plain, (![D_445]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_445)=k7_relat_1('#skF_5', D_445) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_1439])).
% 5.98/2.10  tff(c_1449, plain, (![D_445]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_445)=k7_relat_1('#skF_5', D_445))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1443])).
% 5.98/2.10  tff(c_1441, plain, (![D_445]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_445)=k7_relat_1('#skF_6', D_445) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_1439])).
% 5.98/2.10  tff(c_1446, plain, (![D_445]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_445)=k7_relat_1('#skF_6', D_445))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1441])).
% 5.98/2.10  tff(c_38, plain, (![A_152, C_154, D_155, F_157, E_156, B_153]: (v1_funct_2(k1_tmap_1(A_152, B_153, C_154, D_155, E_156, F_157), k4_subset_1(A_152, C_154, D_155), B_153) | ~m1_subset_1(F_157, k1_zfmisc_1(k2_zfmisc_1(D_155, B_153))) | ~v1_funct_2(F_157, D_155, B_153) | ~v1_funct_1(F_157) | ~m1_subset_1(E_156, k1_zfmisc_1(k2_zfmisc_1(C_154, B_153))) | ~v1_funct_2(E_156, C_154, B_153) | ~v1_funct_1(E_156) | ~m1_subset_1(D_155, k1_zfmisc_1(A_152)) | v1_xboole_0(D_155) | ~m1_subset_1(C_154, k1_zfmisc_1(A_152)) | v1_xboole_0(C_154) | v1_xboole_0(B_153) | v1_xboole_0(A_152))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.98/2.10  tff(c_36, plain, (![A_152, C_154, D_155, F_157, E_156, B_153]: (m1_subset_1(k1_tmap_1(A_152, B_153, C_154, D_155, E_156, F_157), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_152, C_154, D_155), B_153))) | ~m1_subset_1(F_157, k1_zfmisc_1(k2_zfmisc_1(D_155, B_153))) | ~v1_funct_2(F_157, D_155, B_153) | ~v1_funct_1(F_157) | ~m1_subset_1(E_156, k1_zfmisc_1(k2_zfmisc_1(C_154, B_153))) | ~v1_funct_2(E_156, C_154, B_153) | ~v1_funct_1(E_156) | ~m1_subset_1(D_155, k1_zfmisc_1(A_152)) | v1_xboole_0(D_155) | ~m1_subset_1(C_154, k1_zfmisc_1(A_152)) | v1_xboole_0(C_154) | v1_xboole_0(B_153) | v1_xboole_0(A_152))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.98/2.10  tff(c_1617, plain, (![F_486, D_490, C_488, A_485, E_489, B_487]: (k2_partfun1(k4_subset_1(A_485, C_488, D_490), B_487, k1_tmap_1(A_485, B_487, C_488, D_490, E_489, F_486), C_488)=E_489 | ~m1_subset_1(k1_tmap_1(A_485, B_487, C_488, D_490, E_489, F_486), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_485, C_488, D_490), B_487))) | ~v1_funct_2(k1_tmap_1(A_485, B_487, C_488, D_490, E_489, F_486), k4_subset_1(A_485, C_488, D_490), B_487) | ~v1_funct_1(k1_tmap_1(A_485, B_487, C_488, D_490, E_489, F_486)) | k2_partfun1(D_490, B_487, F_486, k9_subset_1(A_485, C_488, D_490))!=k2_partfun1(C_488, B_487, E_489, k9_subset_1(A_485, C_488, D_490)) | ~m1_subset_1(F_486, k1_zfmisc_1(k2_zfmisc_1(D_490, B_487))) | ~v1_funct_2(F_486, D_490, B_487) | ~v1_funct_1(F_486) | ~m1_subset_1(E_489, k1_zfmisc_1(k2_zfmisc_1(C_488, B_487))) | ~v1_funct_2(E_489, C_488, B_487) | ~v1_funct_1(E_489) | ~m1_subset_1(D_490, k1_zfmisc_1(A_485)) | v1_xboole_0(D_490) | ~m1_subset_1(C_488, k1_zfmisc_1(A_485)) | v1_xboole_0(C_488) | v1_xboole_0(B_487) | v1_xboole_0(A_485))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.98/2.10  tff(c_1956, plain, (![D_554, A_551, E_556, C_553, B_555, F_552]: (k2_partfun1(k4_subset_1(A_551, C_553, D_554), B_555, k1_tmap_1(A_551, B_555, C_553, D_554, E_556, F_552), C_553)=E_556 | ~v1_funct_2(k1_tmap_1(A_551, B_555, C_553, D_554, E_556, F_552), k4_subset_1(A_551, C_553, D_554), B_555) | ~v1_funct_1(k1_tmap_1(A_551, B_555, C_553, D_554, E_556, F_552)) | k2_partfun1(D_554, B_555, F_552, k9_subset_1(A_551, C_553, D_554))!=k2_partfun1(C_553, B_555, E_556, k9_subset_1(A_551, C_553, D_554)) | ~m1_subset_1(F_552, k1_zfmisc_1(k2_zfmisc_1(D_554, B_555))) | ~v1_funct_2(F_552, D_554, B_555) | ~v1_funct_1(F_552) | ~m1_subset_1(E_556, k1_zfmisc_1(k2_zfmisc_1(C_553, B_555))) | ~v1_funct_2(E_556, C_553, B_555) | ~v1_funct_1(E_556) | ~m1_subset_1(D_554, k1_zfmisc_1(A_551)) | v1_xboole_0(D_554) | ~m1_subset_1(C_553, k1_zfmisc_1(A_551)) | v1_xboole_0(C_553) | v1_xboole_0(B_555) | v1_xboole_0(A_551))), inference(resolution, [status(thm)], [c_36, c_1617])).
% 5.98/2.10  tff(c_1964, plain, (![F_564, A_563, C_565, B_567, E_568, D_566]: (k2_partfun1(k4_subset_1(A_563, C_565, D_566), B_567, k1_tmap_1(A_563, B_567, C_565, D_566, E_568, F_564), C_565)=E_568 | ~v1_funct_1(k1_tmap_1(A_563, B_567, C_565, D_566, E_568, F_564)) | k2_partfun1(D_566, B_567, F_564, k9_subset_1(A_563, C_565, D_566))!=k2_partfun1(C_565, B_567, E_568, k9_subset_1(A_563, C_565, D_566)) | ~m1_subset_1(F_564, k1_zfmisc_1(k2_zfmisc_1(D_566, B_567))) | ~v1_funct_2(F_564, D_566, B_567) | ~v1_funct_1(F_564) | ~m1_subset_1(E_568, k1_zfmisc_1(k2_zfmisc_1(C_565, B_567))) | ~v1_funct_2(E_568, C_565, B_567) | ~v1_funct_1(E_568) | ~m1_subset_1(D_566, k1_zfmisc_1(A_563)) | v1_xboole_0(D_566) | ~m1_subset_1(C_565, k1_zfmisc_1(A_563)) | v1_xboole_0(C_565) | v1_xboole_0(B_567) | v1_xboole_0(A_563))), inference(resolution, [status(thm)], [c_38, c_1956])).
% 5.98/2.10  tff(c_1968, plain, (![A_563, C_565, E_568]: (k2_partfun1(k4_subset_1(A_563, C_565, '#skF_4'), '#skF_2', k1_tmap_1(A_563, '#skF_2', C_565, '#skF_4', E_568, '#skF_6'), C_565)=E_568 | ~v1_funct_1(k1_tmap_1(A_563, '#skF_2', C_565, '#skF_4', E_568, '#skF_6')) | k2_partfun1(C_565, '#skF_2', E_568, k9_subset_1(A_563, C_565, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_563, C_565, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_568, k1_zfmisc_1(k2_zfmisc_1(C_565, '#skF_2'))) | ~v1_funct_2(E_568, C_565, '#skF_2') | ~v1_funct_1(E_568) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_563)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_565, k1_zfmisc_1(A_563)) | v1_xboole_0(C_565) | v1_xboole_0('#skF_2') | v1_xboole_0(A_563))), inference(resolution, [status(thm)], [c_44, c_1964])).
% 5.98/2.10  tff(c_1974, plain, (![A_563, C_565, E_568]: (k2_partfun1(k4_subset_1(A_563, C_565, '#skF_4'), '#skF_2', k1_tmap_1(A_563, '#skF_2', C_565, '#skF_4', E_568, '#skF_6'), C_565)=E_568 | ~v1_funct_1(k1_tmap_1(A_563, '#skF_2', C_565, '#skF_4', E_568, '#skF_6')) | k2_partfun1(C_565, '#skF_2', E_568, k9_subset_1(A_563, C_565, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_563, C_565, '#skF_4')) | ~m1_subset_1(E_568, k1_zfmisc_1(k2_zfmisc_1(C_565, '#skF_2'))) | ~v1_funct_2(E_568, C_565, '#skF_2') | ~v1_funct_1(E_568) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_563)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_565, k1_zfmisc_1(A_563)) | v1_xboole_0(C_565) | v1_xboole_0('#skF_2') | v1_xboole_0(A_563))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1446, c_1968])).
% 5.98/2.10  tff(c_1980, plain, (![A_569, C_570, E_571]: (k2_partfun1(k4_subset_1(A_569, C_570, '#skF_4'), '#skF_2', k1_tmap_1(A_569, '#skF_2', C_570, '#skF_4', E_571, '#skF_6'), C_570)=E_571 | ~v1_funct_1(k1_tmap_1(A_569, '#skF_2', C_570, '#skF_4', E_571, '#skF_6')) | k2_partfun1(C_570, '#skF_2', E_571, k9_subset_1(A_569, C_570, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_569, C_570, '#skF_4')) | ~m1_subset_1(E_571, k1_zfmisc_1(k2_zfmisc_1(C_570, '#skF_2'))) | ~v1_funct_2(E_571, C_570, '#skF_2') | ~v1_funct_1(E_571) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_569)) | ~m1_subset_1(C_570, k1_zfmisc_1(A_569)) | v1_xboole_0(C_570) | v1_xboole_0(A_569))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_1974])).
% 5.98/2.10  tff(c_1987, plain, (![A_569]: (k2_partfun1(k4_subset_1(A_569, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_569, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_569, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_569, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_569, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_569)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_569)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_569))), inference(resolution, [status(thm)], [c_50, c_1980])).
% 5.98/2.10  tff(c_1997, plain, (![A_569]: (k2_partfun1(k4_subset_1(A_569, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_569, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_569, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_569, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_569, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_569)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_569)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_569))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1449, c_1987])).
% 5.98/2.10  tff(c_2021, plain, (![A_573]: (k2_partfun1(k4_subset_1(A_573, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_573, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_573, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_573, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_573, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_573)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_573)) | v1_xboole_0(A_573))), inference(negUnitSimplification, [status(thm)], [c_64, c_1997])).
% 5.98/2.10  tff(c_577, plain, (![A_284, B_285]: (k3_xboole_0(A_284, B_285)=k1_xboole_0 | ~r1_subset_1(A_284, B_285) | v1_xboole_0(B_285) | v1_xboole_0(A_284))), inference(resolution, [status(thm)], [c_418, c_2])).
% 5.98/2.10  tff(c_580, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_577])).
% 5.98/2.10  tff(c_583, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_60, c_580])).
% 5.98/2.10  tff(c_523, plain, (![A_277, B_278, C_279]: (k9_subset_1(A_277, B_278, C_279)=k3_xboole_0(B_278, C_279) | ~m1_subset_1(C_279, k1_zfmisc_1(A_277)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.98/2.10  tff(c_535, plain, (![B_278]: (k9_subset_1('#skF_1', B_278, '#skF_4')=k3_xboole_0(B_278, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_523])).
% 5.98/2.10  tff(c_688, plain, (![B_301, C_299, E_302, D_300, F_298, A_297]: (v1_funct_1(k1_tmap_1(A_297, B_301, C_299, D_300, E_302, F_298)) | ~m1_subset_1(F_298, k1_zfmisc_1(k2_zfmisc_1(D_300, B_301))) | ~v1_funct_2(F_298, D_300, B_301) | ~v1_funct_1(F_298) | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(C_299, B_301))) | ~v1_funct_2(E_302, C_299, B_301) | ~v1_funct_1(E_302) | ~m1_subset_1(D_300, k1_zfmisc_1(A_297)) | v1_xboole_0(D_300) | ~m1_subset_1(C_299, k1_zfmisc_1(A_297)) | v1_xboole_0(C_299) | v1_xboole_0(B_301) | v1_xboole_0(A_297))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.98/2.10  tff(c_690, plain, (![A_297, C_299, E_302]: (v1_funct_1(k1_tmap_1(A_297, '#skF_2', C_299, '#skF_4', E_302, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(C_299, '#skF_2'))) | ~v1_funct_2(E_302, C_299, '#skF_2') | ~v1_funct_1(E_302) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_297)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_299, k1_zfmisc_1(A_297)) | v1_xboole_0(C_299) | v1_xboole_0('#skF_2') | v1_xboole_0(A_297))), inference(resolution, [status(thm)], [c_44, c_688])).
% 5.98/2.10  tff(c_695, plain, (![A_297, C_299, E_302]: (v1_funct_1(k1_tmap_1(A_297, '#skF_2', C_299, '#skF_4', E_302, '#skF_6')) | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(C_299, '#skF_2'))) | ~v1_funct_2(E_302, C_299, '#skF_2') | ~v1_funct_1(E_302) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_297)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_299, k1_zfmisc_1(A_297)) | v1_xboole_0(C_299) | v1_xboole_0('#skF_2') | v1_xboole_0(A_297))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_690])).
% 5.98/2.10  tff(c_701, plain, (![A_303, C_304, E_305]: (v1_funct_1(k1_tmap_1(A_303, '#skF_2', C_304, '#skF_4', E_305, '#skF_6')) | ~m1_subset_1(E_305, k1_zfmisc_1(k2_zfmisc_1(C_304, '#skF_2'))) | ~v1_funct_2(E_305, C_304, '#skF_2') | ~v1_funct_1(E_305) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_303)) | ~m1_subset_1(C_304, k1_zfmisc_1(A_303)) | v1_xboole_0(C_304) | v1_xboole_0(A_303))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_695])).
% 5.98/2.10  tff(c_705, plain, (![A_303]: (v1_funct_1(k1_tmap_1(A_303, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_303)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_303)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_303))), inference(resolution, [status(thm)], [c_50, c_701])).
% 5.98/2.10  tff(c_712, plain, (![A_303]: (v1_funct_1(k1_tmap_1(A_303, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_303)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_303)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_303))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_705])).
% 5.98/2.10  tff(c_721, plain, (![A_307]: (v1_funct_1(k1_tmap_1(A_307, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_307)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_307)) | v1_xboole_0(A_307))), inference(negUnitSimplification, [status(thm)], [c_64, c_712])).
% 5.98/2.10  tff(c_724, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_721])).
% 5.98/2.10  tff(c_727, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_724])).
% 5.98/2.10  tff(c_728, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_68, c_727])).
% 5.98/2.10  tff(c_645, plain, (![A_291, B_292, C_293, D_294]: (k2_partfun1(A_291, B_292, C_293, D_294)=k7_relat_1(C_293, D_294) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))) | ~v1_funct_1(C_293))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.98/2.10  tff(c_649, plain, (![D_294]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_294)=k7_relat_1('#skF_5', D_294) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_645])).
% 5.98/2.10  tff(c_655, plain, (![D_294]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_294)=k7_relat_1('#skF_5', D_294))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_649])).
% 5.98/2.10  tff(c_647, plain, (![D_294]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_294)=k7_relat_1('#skF_6', D_294) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_645])).
% 5.98/2.10  tff(c_652, plain, (![D_294]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_294)=k7_relat_1('#skF_6', D_294))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_647])).
% 5.98/2.10  tff(c_952, plain, (![C_349, F_347, D_351, A_346, B_348, E_350]: (k2_partfun1(k4_subset_1(A_346, C_349, D_351), B_348, k1_tmap_1(A_346, B_348, C_349, D_351, E_350, F_347), D_351)=F_347 | ~m1_subset_1(k1_tmap_1(A_346, B_348, C_349, D_351, E_350, F_347), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_346, C_349, D_351), B_348))) | ~v1_funct_2(k1_tmap_1(A_346, B_348, C_349, D_351, E_350, F_347), k4_subset_1(A_346, C_349, D_351), B_348) | ~v1_funct_1(k1_tmap_1(A_346, B_348, C_349, D_351, E_350, F_347)) | k2_partfun1(D_351, B_348, F_347, k9_subset_1(A_346, C_349, D_351))!=k2_partfun1(C_349, B_348, E_350, k9_subset_1(A_346, C_349, D_351)) | ~m1_subset_1(F_347, k1_zfmisc_1(k2_zfmisc_1(D_351, B_348))) | ~v1_funct_2(F_347, D_351, B_348) | ~v1_funct_1(F_347) | ~m1_subset_1(E_350, k1_zfmisc_1(k2_zfmisc_1(C_349, B_348))) | ~v1_funct_2(E_350, C_349, B_348) | ~v1_funct_1(E_350) | ~m1_subset_1(D_351, k1_zfmisc_1(A_346)) | v1_xboole_0(D_351) | ~m1_subset_1(C_349, k1_zfmisc_1(A_346)) | v1_xboole_0(C_349) | v1_xboole_0(B_348) | v1_xboole_0(A_346))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.98/2.10  tff(c_1120, plain, (![B_404, F_401, C_402, D_403, A_400, E_405]: (k2_partfun1(k4_subset_1(A_400, C_402, D_403), B_404, k1_tmap_1(A_400, B_404, C_402, D_403, E_405, F_401), D_403)=F_401 | ~v1_funct_2(k1_tmap_1(A_400, B_404, C_402, D_403, E_405, F_401), k4_subset_1(A_400, C_402, D_403), B_404) | ~v1_funct_1(k1_tmap_1(A_400, B_404, C_402, D_403, E_405, F_401)) | k2_partfun1(D_403, B_404, F_401, k9_subset_1(A_400, C_402, D_403))!=k2_partfun1(C_402, B_404, E_405, k9_subset_1(A_400, C_402, D_403)) | ~m1_subset_1(F_401, k1_zfmisc_1(k2_zfmisc_1(D_403, B_404))) | ~v1_funct_2(F_401, D_403, B_404) | ~v1_funct_1(F_401) | ~m1_subset_1(E_405, k1_zfmisc_1(k2_zfmisc_1(C_402, B_404))) | ~v1_funct_2(E_405, C_402, B_404) | ~v1_funct_1(E_405) | ~m1_subset_1(D_403, k1_zfmisc_1(A_400)) | v1_xboole_0(D_403) | ~m1_subset_1(C_402, k1_zfmisc_1(A_400)) | v1_xboole_0(C_402) | v1_xboole_0(B_404) | v1_xboole_0(A_400))), inference(resolution, [status(thm)], [c_36, c_952])).
% 5.98/2.10  tff(c_1124, plain, (![D_409, C_408, F_407, B_410, E_411, A_406]: (k2_partfun1(k4_subset_1(A_406, C_408, D_409), B_410, k1_tmap_1(A_406, B_410, C_408, D_409, E_411, F_407), D_409)=F_407 | ~v1_funct_1(k1_tmap_1(A_406, B_410, C_408, D_409, E_411, F_407)) | k2_partfun1(D_409, B_410, F_407, k9_subset_1(A_406, C_408, D_409))!=k2_partfun1(C_408, B_410, E_411, k9_subset_1(A_406, C_408, D_409)) | ~m1_subset_1(F_407, k1_zfmisc_1(k2_zfmisc_1(D_409, B_410))) | ~v1_funct_2(F_407, D_409, B_410) | ~v1_funct_1(F_407) | ~m1_subset_1(E_411, k1_zfmisc_1(k2_zfmisc_1(C_408, B_410))) | ~v1_funct_2(E_411, C_408, B_410) | ~v1_funct_1(E_411) | ~m1_subset_1(D_409, k1_zfmisc_1(A_406)) | v1_xboole_0(D_409) | ~m1_subset_1(C_408, k1_zfmisc_1(A_406)) | v1_xboole_0(C_408) | v1_xboole_0(B_410) | v1_xboole_0(A_406))), inference(resolution, [status(thm)], [c_38, c_1120])).
% 5.98/2.10  tff(c_1128, plain, (![A_406, C_408, E_411]: (k2_partfun1(k4_subset_1(A_406, C_408, '#skF_4'), '#skF_2', k1_tmap_1(A_406, '#skF_2', C_408, '#skF_4', E_411, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_406, '#skF_2', C_408, '#skF_4', E_411, '#skF_6')) | k2_partfun1(C_408, '#skF_2', E_411, k9_subset_1(A_406, C_408, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_406, C_408, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_411, k1_zfmisc_1(k2_zfmisc_1(C_408, '#skF_2'))) | ~v1_funct_2(E_411, C_408, '#skF_2') | ~v1_funct_1(E_411) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_406)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_408, k1_zfmisc_1(A_406)) | v1_xboole_0(C_408) | v1_xboole_0('#skF_2') | v1_xboole_0(A_406))), inference(resolution, [status(thm)], [c_44, c_1124])).
% 5.98/2.10  tff(c_1134, plain, (![A_406, C_408, E_411]: (k2_partfun1(k4_subset_1(A_406, C_408, '#skF_4'), '#skF_2', k1_tmap_1(A_406, '#skF_2', C_408, '#skF_4', E_411, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_406, '#skF_2', C_408, '#skF_4', E_411, '#skF_6')) | k2_partfun1(C_408, '#skF_2', E_411, k9_subset_1(A_406, C_408, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_406, C_408, '#skF_4')) | ~m1_subset_1(E_411, k1_zfmisc_1(k2_zfmisc_1(C_408, '#skF_2'))) | ~v1_funct_2(E_411, C_408, '#skF_2') | ~v1_funct_1(E_411) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_406)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_408, k1_zfmisc_1(A_406)) | v1_xboole_0(C_408) | v1_xboole_0('#skF_2') | v1_xboole_0(A_406))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_652, c_1128])).
% 5.98/2.10  tff(c_1140, plain, (![A_412, C_413, E_414]: (k2_partfun1(k4_subset_1(A_412, C_413, '#skF_4'), '#skF_2', k1_tmap_1(A_412, '#skF_2', C_413, '#skF_4', E_414, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_412, '#skF_2', C_413, '#skF_4', E_414, '#skF_6')) | k2_partfun1(C_413, '#skF_2', E_414, k9_subset_1(A_412, C_413, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_412, C_413, '#skF_4')) | ~m1_subset_1(E_414, k1_zfmisc_1(k2_zfmisc_1(C_413, '#skF_2'))) | ~v1_funct_2(E_414, C_413, '#skF_2') | ~v1_funct_1(E_414) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_412)) | ~m1_subset_1(C_413, k1_zfmisc_1(A_412)) | v1_xboole_0(C_413) | v1_xboole_0(A_412))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_1134])).
% 5.98/2.10  tff(c_1147, plain, (![A_412]: (k2_partfun1(k4_subset_1(A_412, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_412, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_412, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_412, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_412, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_412)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_412)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_412))), inference(resolution, [status(thm)], [c_50, c_1140])).
% 5.98/2.10  tff(c_1157, plain, (![A_412]: (k2_partfun1(k4_subset_1(A_412, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_412, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_412, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_412, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_412, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_412)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_412)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_412))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_655, c_1147])).
% 5.98/2.10  tff(c_1216, plain, (![A_423]: (k2_partfun1(k4_subset_1(A_423, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_423, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_423, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_423, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_423, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_423)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_423)) | v1_xboole_0(A_423))), inference(negUnitSimplification, [status(thm)], [c_64, c_1157])).
% 5.98/2.10  tff(c_127, plain, (![C_230, A_231, B_232]: (v1_relat_1(C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.98/2.10  tff(c_134, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_127])).
% 5.98/2.10  tff(c_122, plain, (![A_228, B_229]: (v1_xboole_0(k7_relat_1(A_228, B_229)) | ~v1_xboole_0(B_229) | ~v1_relat_1(A_228))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.98/2.10  tff(c_136, plain, (![A_233, B_234]: (k7_relat_1(A_233, B_234)=k1_xboole_0 | ~v1_xboole_0(B_234) | ~v1_relat_1(A_233))), inference(resolution, [status(thm)], [c_122, c_8])).
% 5.98/2.10  tff(c_143, plain, (![A_235]: (k7_relat_1(A_235, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_235))), inference(resolution, [status(thm)], [c_6, c_136])).
% 5.98/2.10  tff(c_154, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_134, c_143])).
% 5.98/2.10  tff(c_135, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_127])).
% 5.98/2.10  tff(c_153, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_135, c_143])).
% 5.98/2.10  tff(c_188, plain, (![A_236, B_237]: (r1_xboole_0(A_236, B_237) | ~r1_subset_1(A_236, B_237) | v1_xboole_0(B_237) | v1_xboole_0(A_236))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.98/2.10  tff(c_341, plain, (![A_257, B_258]: (k3_xboole_0(A_257, B_258)=k1_xboole_0 | ~r1_subset_1(A_257, B_258) | v1_xboole_0(B_258) | v1_xboole_0(A_257))), inference(resolution, [status(thm)], [c_188, c_2])).
% 5.98/2.10  tff(c_347, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_341])).
% 5.98/2.10  tff(c_351, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_60, c_347])).
% 5.98/2.10  tff(c_310, plain, (![A_249, B_250, C_251, D_252]: (k2_partfun1(A_249, B_250, C_251, D_252)=k7_relat_1(C_251, D_252) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))) | ~v1_funct_1(C_251))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.98/2.10  tff(c_314, plain, (![D_252]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_252)=k7_relat_1('#skF_5', D_252) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_310])).
% 5.98/2.10  tff(c_320, plain, (![D_252]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_252)=k7_relat_1('#skF_5', D_252))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_314])).
% 5.98/2.10  tff(c_312, plain, (![D_252]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_252)=k7_relat_1('#skF_6', D_252) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_310])).
% 5.98/2.10  tff(c_317, plain, (![D_252]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_252)=k7_relat_1('#skF_6', D_252))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_312])).
% 5.98/2.10  tff(c_260, plain, (![A_242, B_243, C_244]: (k9_subset_1(A_242, B_243, C_244)=k3_xboole_0(B_243, C_244) | ~m1_subset_1(C_244, k1_zfmisc_1(A_242)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.98/2.10  tff(c_272, plain, (![B_243]: (k9_subset_1('#skF_1', B_243, '#skF_4')=k3_xboole_0(B_243, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_260])).
% 5.98/2.10  tff(c_42, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.98/2.10  tff(c_99, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_42])).
% 5.98/2.10  tff(c_282, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_272, c_99])).
% 5.98/2.10  tff(c_340, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_317, c_282])).
% 5.98/2.10  tff(c_352, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_351, c_351, c_340])).
% 5.98/2.10  tff(c_355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_153, c_352])).
% 5.98/2.10  tff(c_356, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_42])).
% 5.98/2.10  tff(c_455, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_356])).
% 5.98/2.10  tff(c_1227, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1216, c_455])).
% 5.98/2.10  tff(c_1241, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_416, c_583, c_415, c_583, c_535, c_535, c_728, c_1227])).
% 5.98/2.10  tff(c_1243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1241])).
% 5.98/2.10  tff(c_1244, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_356])).
% 5.98/2.10  tff(c_2030, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2021, c_1244])).
% 5.98/2.10  tff(c_2041, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_416, c_1373, c_415, c_1373, c_1325, c_1325, c_1522, c_2030])).
% 5.98/2.10  tff(c_2043, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2041])).
% 5.98/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.98/2.10  
% 5.98/2.10  Inference rules
% 5.98/2.10  ----------------------
% 5.98/2.10  #Ref     : 0
% 5.98/2.10  #Sup     : 422
% 5.98/2.10  #Fact    : 0
% 5.98/2.10  #Define  : 0
% 5.98/2.10  #Split   : 6
% 5.98/2.10  #Chain   : 0
% 5.98/2.10  #Close   : 0
% 5.98/2.10  
% 5.98/2.10  Ordering : KBO
% 5.98/2.10  
% 5.98/2.10  Simplification rules
% 5.98/2.10  ----------------------
% 5.98/2.10  #Subsume      : 39
% 5.98/2.10  #Demod        : 397
% 5.98/2.10  #Tautology    : 206
% 5.98/2.10  #SimpNegUnit  : 100
% 5.98/2.11  #BackRed      : 8
% 5.98/2.11  
% 5.98/2.11  #Partial instantiations: 0
% 5.98/2.11  #Strategies tried      : 1
% 5.98/2.11  
% 5.98/2.11  Timing (in seconds)
% 5.98/2.11  ----------------------
% 5.98/2.11  Preprocessing        : 0.48
% 5.98/2.11  Parsing              : 0.24
% 5.98/2.11  CNF conversion       : 0.06
% 5.98/2.11  Main loop            : 0.82
% 5.98/2.11  Inferencing          : 0.28
% 5.98/2.11  Reduction            : 0.25
% 5.98/2.11  Demodulation         : 0.17
% 5.98/2.11  BG Simplification    : 0.04
% 5.98/2.11  Subsumption          : 0.19
% 5.98/2.11  Abstraction          : 0.05
% 5.98/2.11  MUC search           : 0.00
% 5.98/2.11  Cooper               : 0.00
% 5.98/2.11  Total                : 1.35
% 5.98/2.11  Index Insertion      : 0.00
% 5.98/2.11  Index Deletion       : 0.00
% 5.98/2.11  Index Matching       : 0.00
% 5.98/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
