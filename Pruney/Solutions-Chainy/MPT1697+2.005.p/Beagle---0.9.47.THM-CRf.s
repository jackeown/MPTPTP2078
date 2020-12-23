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
% DateTime   : Thu Dec  3 10:26:08 EST 2020

% Result     : Theorem 13.39s
% Output     : CNFRefutation 13.80s
% Verified   : 
% Statistics : Number of formulae       :  249 ( 753 expanded)
%              Number of leaves         :   44 ( 286 expanded)
%              Depth                    :   15
%              Number of atoms          :  783 (3858 expanded)
%              Number of equality atoms :  156 ( 715 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_233,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
       => r1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

tff(f_191,axiom,(
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

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_157,axiom,(
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

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_1710,plain,(
    ! [C_346,A_347,B_348] :
      ( v1_relat_1(C_346)
      | ~ m1_subset_1(C_346,k1_zfmisc_1(k2_zfmisc_1(A_347,B_348))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1718,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_1710])).

tff(c_82,plain,(
    ! [B_227,A_228] : k3_xboole_0(B_227,A_228) = k3_xboole_0(A_228,B_227) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ! [A_228] : k3_xboole_0(k1_xboole_0,A_228) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_4])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_62,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(A_16,B_17)
      | ~ r1_subset_1(A_16,B_17)
      | v1_xboole_0(B_17)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_1749,plain,(
    ! [C_354,A_355,B_356] :
      ( v4_relat_1(C_354,A_355)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(A_355,B_356))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1757,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1749])).

tff(c_1786,plain,(
    ! [B_366,A_367] :
      ( k1_relat_1(B_366) = A_367
      | ~ v1_partfun1(B_366,A_367)
      | ~ v4_relat_1(B_366,A_367)
      | ~ v1_relat_1(B_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1789,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1757,c_1786])).

tff(c_1795,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1718,c_1789])).

tff(c_1799,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1795])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_3008,plain,(
    ! [C_426,A_427,B_428] :
      ( v1_partfun1(C_426,A_427)
      | ~ v1_funct_2(C_426,A_427,B_428)
      | ~ v1_funct_1(C_426)
      | ~ m1_subset_1(C_426,k1_zfmisc_1(k2_zfmisc_1(A_427,B_428)))
      | v1_xboole_0(B_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3014,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_3008])).

tff(c_3021,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3014])).

tff(c_3023,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1799,c_3021])).

tff(c_3024,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1795])).

tff(c_12,plain,(
    ! [A_13,B_15] :
      ( k7_relat_1(A_13,B_15) = k1_xboole_0
      | ~ r1_xboole_0(B_15,k1_relat_1(A_13))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3032,plain,(
    ! [B_15] :
      ( k7_relat_1('#skF_6',B_15) = k1_xboole_0
      | ~ r1_xboole_0(B_15,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3024,c_12])).

tff(c_24333,plain,(
    ! [B_1027] :
      ( k7_relat_1('#skF_6',B_1027) = k1_xboole_0
      | ~ r1_xboole_0(B_1027,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1718,c_3032])).

tff(c_24337,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_6',A_16) = k1_xboole_0
      | ~ r1_subset_1(A_16,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_16,c_24333])).

tff(c_24352,plain,(
    ! [A_1029] :
      ( k7_relat_1('#skF_6',A_1029) = k1_xboole_0
      | ~ r1_subset_1(A_1029,'#skF_4')
      | v1_xboole_0(A_1029) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_24337])).

tff(c_24355,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_24352])).

tff(c_24358,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_24355])).

tff(c_24414,plain,(
    ! [C_1037,A_1038,B_1039] :
      ( k3_xboole_0(k7_relat_1(C_1037,A_1038),k7_relat_1(C_1037,B_1039)) = k7_relat_1(C_1037,k3_xboole_0(A_1038,B_1039))
      | ~ v1_relat_1(C_1037) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24429,plain,(
    ! [B_1039] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_1039)) = k3_xboole_0(k1_xboole_0,k7_relat_1('#skF_6',B_1039))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24358,c_24414])).

tff(c_24448,plain,(
    ! [B_1039] : k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_1039)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1718,c_98,c_24429])).

tff(c_24359,plain,(
    ! [A_1030,B_1031,C_1032] :
      ( k9_subset_1(A_1030,B_1031,C_1032) = k3_xboole_0(B_1031,C_1032)
      | ~ m1_subset_1(C_1032,k1_zfmisc_1(A_1030)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24371,plain,(
    ! [B_1031] : k9_subset_1('#skF_1',B_1031,'#skF_4') = k3_xboole_0(B_1031,'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_24359])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_1717,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_1710])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1759,plain,(
    ! [B_359,A_360] :
      ( r1_subset_1(B_359,A_360)
      | ~ r1_subset_1(A_360,B_359)
      | v1_xboole_0(B_359)
      | v1_xboole_0(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1761,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1759])).

tff(c_1764,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_1761])).

tff(c_1756,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1749])).

tff(c_1792,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1756,c_1786])).

tff(c_1798,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1717,c_1792])).

tff(c_23720,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1798])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_24292,plain,(
    ! [C_1023,A_1024,B_1025] :
      ( v1_partfun1(C_1023,A_1024)
      | ~ v1_funct_2(C_1023,A_1024,B_1025)
      | ~ v1_funct_1(C_1023)
      | ~ m1_subset_1(C_1023,k1_zfmisc_1(k2_zfmisc_1(A_1024,B_1025)))
      | v1_xboole_0(B_1025) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_24295,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_24292])).

tff(c_24301,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_24295])).

tff(c_24303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_23720,c_24301])).

tff(c_24304,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1798])).

tff(c_24312,plain,(
    ! [B_15] :
      ( k7_relat_1('#skF_5',B_15) = k1_xboole_0
      | ~ r1_xboole_0(B_15,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24304,c_12])).

tff(c_24325,plain,(
    ! [B_1026] :
      ( k7_relat_1('#skF_5',B_1026) = k1_xboole_0
      | ~ r1_xboole_0(B_1026,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1717,c_24312])).

tff(c_24329,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_5',A_16) = k1_xboole_0
      | ~ r1_subset_1(A_16,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_16,c_24325])).

tff(c_24341,plain,(
    ! [A_1028] :
      ( k7_relat_1('#skF_5',A_1028) = k1_xboole_0
      | ~ r1_subset_1(A_1028,'#skF_3')
      | v1_xboole_0(A_1028) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_24329])).

tff(c_24344,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1764,c_24341])).

tff(c_24347,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_24344])).

tff(c_24438,plain,(
    ! [A_1038] :
      ( k7_relat_1('#skF_5',k3_xboole_0(A_1038,'#skF_4')) = k3_xboole_0(k7_relat_1('#skF_5',A_1038),k1_xboole_0)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24347,c_24414])).

tff(c_24454,plain,(
    ! [A_1038] : k7_relat_1('#skF_5',k3_xboole_0(A_1038,'#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1717,c_98,c_2,c_24438])).

tff(c_25195,plain,(
    ! [A_1073,F_1070,B_1072,D_1069,E_1074,C_1071] :
      ( v1_funct_1(k1_tmap_1(A_1073,B_1072,C_1071,D_1069,E_1074,F_1070))
      | ~ m1_subset_1(F_1070,k1_zfmisc_1(k2_zfmisc_1(D_1069,B_1072)))
      | ~ v1_funct_2(F_1070,D_1069,B_1072)
      | ~ v1_funct_1(F_1070)
      | ~ m1_subset_1(E_1074,k1_zfmisc_1(k2_zfmisc_1(C_1071,B_1072)))
      | ~ v1_funct_2(E_1074,C_1071,B_1072)
      | ~ v1_funct_1(E_1074)
      | ~ m1_subset_1(D_1069,k1_zfmisc_1(A_1073))
      | v1_xboole_0(D_1069)
      | ~ m1_subset_1(C_1071,k1_zfmisc_1(A_1073))
      | v1_xboole_0(C_1071)
      | v1_xboole_0(B_1072)
      | v1_xboole_0(A_1073) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_25199,plain,(
    ! [A_1073,C_1071,E_1074] :
      ( v1_funct_1(k1_tmap_1(A_1073,'#skF_2',C_1071,'#skF_4',E_1074,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1074,k1_zfmisc_1(k2_zfmisc_1(C_1071,'#skF_2')))
      | ~ v1_funct_2(E_1074,C_1071,'#skF_2')
      | ~ v1_funct_1(E_1074)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1073))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1071,k1_zfmisc_1(A_1073))
      | v1_xboole_0(C_1071)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1073) ) ),
    inference(resolution,[status(thm)],[c_50,c_25195])).

tff(c_25206,plain,(
    ! [A_1073,C_1071,E_1074] :
      ( v1_funct_1(k1_tmap_1(A_1073,'#skF_2',C_1071,'#skF_4',E_1074,'#skF_6'))
      | ~ m1_subset_1(E_1074,k1_zfmisc_1(k2_zfmisc_1(C_1071,'#skF_2')))
      | ~ v1_funct_2(E_1074,C_1071,'#skF_2')
      | ~ v1_funct_1(E_1074)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1073))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1071,k1_zfmisc_1(A_1073))
      | v1_xboole_0(C_1071)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1073) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_25199])).

tff(c_25211,plain,(
    ! [A_1075,C_1076,E_1077] :
      ( v1_funct_1(k1_tmap_1(A_1075,'#skF_2',C_1076,'#skF_4',E_1077,'#skF_6'))
      | ~ m1_subset_1(E_1077,k1_zfmisc_1(k2_zfmisc_1(C_1076,'#skF_2')))
      | ~ v1_funct_2(E_1077,C_1076,'#skF_2')
      | ~ v1_funct_1(E_1077)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1075))
      | ~ m1_subset_1(C_1076,k1_zfmisc_1(A_1075))
      | v1_xboole_0(C_1076)
      | v1_xboole_0(A_1075) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_25206])).

tff(c_25213,plain,(
    ! [A_1075] :
      ( v1_funct_1(k1_tmap_1(A_1075,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1075))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1075))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1075) ) ),
    inference(resolution,[status(thm)],[c_56,c_25211])).

tff(c_25218,plain,(
    ! [A_1075] :
      ( v1_funct_1(k1_tmap_1(A_1075,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1075))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1075))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1075) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_25213])).

tff(c_26303,plain,(
    ! [A_1121] :
      ( v1_funct_1(k1_tmap_1(A_1121,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1121))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1121))
      | v1_xboole_0(A_1121) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_25218])).

tff(c_26306,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_26303])).

tff(c_26309,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_26306])).

tff(c_26310,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_26309])).

tff(c_24674,plain,(
    ! [A_1046,B_1047,C_1048,D_1049] :
      ( k2_partfun1(A_1046,B_1047,C_1048,D_1049) = k7_relat_1(C_1048,D_1049)
      | ~ m1_subset_1(C_1048,k1_zfmisc_1(k2_zfmisc_1(A_1046,B_1047)))
      | ~ v1_funct_1(C_1048) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_24676,plain,(
    ! [D_1049] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_1049) = k7_relat_1('#skF_5',D_1049)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_24674])).

tff(c_24681,plain,(
    ! [D_1049] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1049) = k7_relat_1('#skF_5',D_1049) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_24676])).

tff(c_24678,plain,(
    ! [D_1049] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_1049) = k7_relat_1('#skF_6',D_1049)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_24674])).

tff(c_24684,plain,(
    ! [D_1049] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_1049) = k7_relat_1('#skF_6',D_1049) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_24678])).

tff(c_44,plain,(
    ! [A_163,C_165,D_166,F_168,B_164,E_167] :
      ( v1_funct_2(k1_tmap_1(A_163,B_164,C_165,D_166,E_167,F_168),k4_subset_1(A_163,C_165,D_166),B_164)
      | ~ m1_subset_1(F_168,k1_zfmisc_1(k2_zfmisc_1(D_166,B_164)))
      | ~ v1_funct_2(F_168,D_166,B_164)
      | ~ v1_funct_1(F_168)
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(C_165,B_164)))
      | ~ v1_funct_2(E_167,C_165,B_164)
      | ~ v1_funct_1(E_167)
      | ~ m1_subset_1(D_166,k1_zfmisc_1(A_163))
      | v1_xboole_0(D_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(A_163))
      | v1_xboole_0(C_165)
      | v1_xboole_0(B_164)
      | v1_xboole_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_42,plain,(
    ! [A_163,C_165,D_166,F_168,B_164,E_167] :
      ( m1_subset_1(k1_tmap_1(A_163,B_164,C_165,D_166,E_167,F_168),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_163,C_165,D_166),B_164)))
      | ~ m1_subset_1(F_168,k1_zfmisc_1(k2_zfmisc_1(D_166,B_164)))
      | ~ v1_funct_2(F_168,D_166,B_164)
      | ~ v1_funct_1(F_168)
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(C_165,B_164)))
      | ~ v1_funct_2(E_167,C_165,B_164)
      | ~ v1_funct_1(E_167)
      | ~ m1_subset_1(D_166,k1_zfmisc_1(A_163))
      | v1_xboole_0(D_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(A_163))
      | v1_xboole_0(C_165)
      | v1_xboole_0(B_164)
      | v1_xboole_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_27166,plain,(
    ! [D_1150,B_1151,F_1154,A_1152,E_1153,C_1149] :
      ( k2_partfun1(k4_subset_1(A_1152,C_1149,D_1150),B_1151,k1_tmap_1(A_1152,B_1151,C_1149,D_1150,E_1153,F_1154),C_1149) = E_1153
      | ~ m1_subset_1(k1_tmap_1(A_1152,B_1151,C_1149,D_1150,E_1153,F_1154),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1152,C_1149,D_1150),B_1151)))
      | ~ v1_funct_2(k1_tmap_1(A_1152,B_1151,C_1149,D_1150,E_1153,F_1154),k4_subset_1(A_1152,C_1149,D_1150),B_1151)
      | ~ v1_funct_1(k1_tmap_1(A_1152,B_1151,C_1149,D_1150,E_1153,F_1154))
      | k2_partfun1(D_1150,B_1151,F_1154,k9_subset_1(A_1152,C_1149,D_1150)) != k2_partfun1(C_1149,B_1151,E_1153,k9_subset_1(A_1152,C_1149,D_1150))
      | ~ m1_subset_1(F_1154,k1_zfmisc_1(k2_zfmisc_1(D_1150,B_1151)))
      | ~ v1_funct_2(F_1154,D_1150,B_1151)
      | ~ v1_funct_1(F_1154)
      | ~ m1_subset_1(E_1153,k1_zfmisc_1(k2_zfmisc_1(C_1149,B_1151)))
      | ~ v1_funct_2(E_1153,C_1149,B_1151)
      | ~ v1_funct_1(E_1153)
      | ~ m1_subset_1(D_1150,k1_zfmisc_1(A_1152))
      | v1_xboole_0(D_1150)
      | ~ m1_subset_1(C_1149,k1_zfmisc_1(A_1152))
      | v1_xboole_0(C_1149)
      | v1_xboole_0(B_1151)
      | v1_xboole_0(A_1152) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_44325,plain,(
    ! [D_1643,B_1646,E_1648,A_1647,C_1645,F_1644] :
      ( k2_partfun1(k4_subset_1(A_1647,C_1645,D_1643),B_1646,k1_tmap_1(A_1647,B_1646,C_1645,D_1643,E_1648,F_1644),C_1645) = E_1648
      | ~ v1_funct_2(k1_tmap_1(A_1647,B_1646,C_1645,D_1643,E_1648,F_1644),k4_subset_1(A_1647,C_1645,D_1643),B_1646)
      | ~ v1_funct_1(k1_tmap_1(A_1647,B_1646,C_1645,D_1643,E_1648,F_1644))
      | k2_partfun1(D_1643,B_1646,F_1644,k9_subset_1(A_1647,C_1645,D_1643)) != k2_partfun1(C_1645,B_1646,E_1648,k9_subset_1(A_1647,C_1645,D_1643))
      | ~ m1_subset_1(F_1644,k1_zfmisc_1(k2_zfmisc_1(D_1643,B_1646)))
      | ~ v1_funct_2(F_1644,D_1643,B_1646)
      | ~ v1_funct_1(F_1644)
      | ~ m1_subset_1(E_1648,k1_zfmisc_1(k2_zfmisc_1(C_1645,B_1646)))
      | ~ v1_funct_2(E_1648,C_1645,B_1646)
      | ~ v1_funct_1(E_1648)
      | ~ m1_subset_1(D_1643,k1_zfmisc_1(A_1647))
      | v1_xboole_0(D_1643)
      | ~ m1_subset_1(C_1645,k1_zfmisc_1(A_1647))
      | v1_xboole_0(C_1645)
      | v1_xboole_0(B_1646)
      | v1_xboole_0(A_1647) ) ),
    inference(resolution,[status(thm)],[c_42,c_27166])).

tff(c_46025,plain,(
    ! [C_1706,F_1705,E_1709,A_1708,D_1704,B_1707] :
      ( k2_partfun1(k4_subset_1(A_1708,C_1706,D_1704),B_1707,k1_tmap_1(A_1708,B_1707,C_1706,D_1704,E_1709,F_1705),C_1706) = E_1709
      | ~ v1_funct_1(k1_tmap_1(A_1708,B_1707,C_1706,D_1704,E_1709,F_1705))
      | k2_partfun1(D_1704,B_1707,F_1705,k9_subset_1(A_1708,C_1706,D_1704)) != k2_partfun1(C_1706,B_1707,E_1709,k9_subset_1(A_1708,C_1706,D_1704))
      | ~ m1_subset_1(F_1705,k1_zfmisc_1(k2_zfmisc_1(D_1704,B_1707)))
      | ~ v1_funct_2(F_1705,D_1704,B_1707)
      | ~ v1_funct_1(F_1705)
      | ~ m1_subset_1(E_1709,k1_zfmisc_1(k2_zfmisc_1(C_1706,B_1707)))
      | ~ v1_funct_2(E_1709,C_1706,B_1707)
      | ~ v1_funct_1(E_1709)
      | ~ m1_subset_1(D_1704,k1_zfmisc_1(A_1708))
      | v1_xboole_0(D_1704)
      | ~ m1_subset_1(C_1706,k1_zfmisc_1(A_1708))
      | v1_xboole_0(C_1706)
      | v1_xboole_0(B_1707)
      | v1_xboole_0(A_1708) ) ),
    inference(resolution,[status(thm)],[c_44,c_44325])).

tff(c_46031,plain,(
    ! [A_1708,C_1706,E_1709] :
      ( k2_partfun1(k4_subset_1(A_1708,C_1706,'#skF_4'),'#skF_2',k1_tmap_1(A_1708,'#skF_2',C_1706,'#skF_4',E_1709,'#skF_6'),C_1706) = E_1709
      | ~ v1_funct_1(k1_tmap_1(A_1708,'#skF_2',C_1706,'#skF_4',E_1709,'#skF_6'))
      | k2_partfun1(C_1706,'#skF_2',E_1709,k9_subset_1(A_1708,C_1706,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1708,C_1706,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1709,k1_zfmisc_1(k2_zfmisc_1(C_1706,'#skF_2')))
      | ~ v1_funct_2(E_1709,C_1706,'#skF_2')
      | ~ v1_funct_1(E_1709)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1708))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1706,k1_zfmisc_1(A_1708))
      | v1_xboole_0(C_1706)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1708) ) ),
    inference(resolution,[status(thm)],[c_50,c_46025])).

tff(c_46039,plain,(
    ! [A_1708,C_1706,E_1709] :
      ( k2_partfun1(k4_subset_1(A_1708,C_1706,'#skF_4'),'#skF_2',k1_tmap_1(A_1708,'#skF_2',C_1706,'#skF_4',E_1709,'#skF_6'),C_1706) = E_1709
      | ~ v1_funct_1(k1_tmap_1(A_1708,'#skF_2',C_1706,'#skF_4',E_1709,'#skF_6'))
      | k2_partfun1(C_1706,'#skF_2',E_1709,k9_subset_1(A_1708,C_1706,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1708,C_1706,'#skF_4'))
      | ~ m1_subset_1(E_1709,k1_zfmisc_1(k2_zfmisc_1(C_1706,'#skF_2')))
      | ~ v1_funct_2(E_1709,C_1706,'#skF_2')
      | ~ v1_funct_1(E_1709)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1708))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1706,k1_zfmisc_1(A_1708))
      | v1_xboole_0(C_1706)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1708) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_24684,c_46031])).

tff(c_46119,plain,(
    ! [A_1730,C_1731,E_1732] :
      ( k2_partfun1(k4_subset_1(A_1730,C_1731,'#skF_4'),'#skF_2',k1_tmap_1(A_1730,'#skF_2',C_1731,'#skF_4',E_1732,'#skF_6'),C_1731) = E_1732
      | ~ v1_funct_1(k1_tmap_1(A_1730,'#skF_2',C_1731,'#skF_4',E_1732,'#skF_6'))
      | k2_partfun1(C_1731,'#skF_2',E_1732,k9_subset_1(A_1730,C_1731,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1730,C_1731,'#skF_4'))
      | ~ m1_subset_1(E_1732,k1_zfmisc_1(k2_zfmisc_1(C_1731,'#skF_2')))
      | ~ v1_funct_2(E_1732,C_1731,'#skF_2')
      | ~ v1_funct_1(E_1732)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1730))
      | ~ m1_subset_1(C_1731,k1_zfmisc_1(A_1730))
      | v1_xboole_0(C_1731)
      | v1_xboole_0(A_1730) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_46039])).

tff(c_46124,plain,(
    ! [A_1730] :
      ( k2_partfun1(k4_subset_1(A_1730,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1730,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1730,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1730,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1730,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1730))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1730))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1730) ) ),
    inference(resolution,[status(thm)],[c_56,c_46119])).

tff(c_46132,plain,(
    ! [A_1730] :
      ( k2_partfun1(k4_subset_1(A_1730,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1730,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1730,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1730,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1730,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1730))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1730))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1730) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_24681,c_46124])).

tff(c_46158,plain,(
    ! [A_1743] :
      ( k2_partfun1(k4_subset_1(A_1743,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1743,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1743,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1743,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1743,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1743))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1743))
      | v1_xboole_0(A_1743) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_46132])).

tff(c_3652,plain,(
    ! [B_463] :
      ( k7_relat_1('#skF_6',B_463) = k1_xboole_0
      | ~ r1_xboole_0(B_463,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1718,c_3032])).

tff(c_3656,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_6',A_16) = k1_xboole_0
      | ~ r1_subset_1(A_16,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_16,c_3652])).

tff(c_3671,plain,(
    ! [A_465] :
      ( k7_relat_1('#skF_6',A_465) = k1_xboole_0
      | ~ r1_subset_1(A_465,'#skF_4')
      | v1_xboole_0(A_465) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3656])).

tff(c_3674,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_3671])).

tff(c_3677,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3674])).

tff(c_3733,plain,(
    ! [C_473,A_474,B_475] :
      ( k3_xboole_0(k7_relat_1(C_473,A_474),k7_relat_1(C_473,B_475)) = k7_relat_1(C_473,k3_xboole_0(A_474,B_475))
      | ~ v1_relat_1(C_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3751,plain,(
    ! [A_474] :
      ( k7_relat_1('#skF_6',k3_xboole_0(A_474,'#skF_3')) = k3_xboole_0(k7_relat_1('#skF_6',A_474),k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3677,c_3733])).

tff(c_3769,plain,(
    ! [A_474] : k7_relat_1('#skF_6',k3_xboole_0(A_474,'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1718,c_98,c_2,c_3751])).

tff(c_3042,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1798])).

tff(c_3615,plain,(
    ! [C_459,A_460,B_461] :
      ( v1_partfun1(C_459,A_460)
      | ~ v1_funct_2(C_459,A_460,B_461)
      | ~ v1_funct_1(C_459)
      | ~ m1_subset_1(C_459,k1_zfmisc_1(k2_zfmisc_1(A_460,B_461)))
      | v1_xboole_0(B_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3618,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_3615])).

tff(c_3624,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3618])).

tff(c_3626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3042,c_3624])).

tff(c_3627,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1798])).

tff(c_3635,plain,(
    ! [B_15] :
      ( k7_relat_1('#skF_5',B_15) = k1_xboole_0
      | ~ r1_xboole_0(B_15,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3627,c_12])).

tff(c_3644,plain,(
    ! [B_462] :
      ( k7_relat_1('#skF_5',B_462) = k1_xboole_0
      | ~ r1_xboole_0(B_462,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1717,c_3635])).

tff(c_3648,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_5',A_16) = k1_xboole_0
      | ~ r1_subset_1(A_16,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_16,c_3644])).

tff(c_3660,plain,(
    ! [A_464] :
      ( k7_relat_1('#skF_5',A_464) = k1_xboole_0
      | ~ r1_subset_1(A_464,'#skF_3')
      | v1_xboole_0(A_464) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3648])).

tff(c_3663,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1764,c_3660])).

tff(c_3666,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3663])).

tff(c_3754,plain,(
    ! [B_475] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_4',B_475)) = k3_xboole_0(k1_xboole_0,k7_relat_1('#skF_5',B_475))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3666,c_3733])).

tff(c_3771,plain,(
    ! [B_475] : k7_relat_1('#skF_5',k3_xboole_0('#skF_4',B_475)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1717,c_98,c_3754])).

tff(c_3678,plain,(
    ! [A_466,B_467,C_468] :
      ( k9_subset_1(A_466,B_467,C_468) = k3_xboole_0(B_467,C_468)
      | ~ m1_subset_1(C_468,k1_zfmisc_1(A_466)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3690,plain,(
    ! [B_467] : k9_subset_1('#skF_1',B_467,'#skF_4') = k3_xboole_0(B_467,'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_3678])).

tff(c_4489,plain,(
    ! [C_507,B_508,D_505,A_509,E_510,F_506] :
      ( v1_funct_1(k1_tmap_1(A_509,B_508,C_507,D_505,E_510,F_506))
      | ~ m1_subset_1(F_506,k1_zfmisc_1(k2_zfmisc_1(D_505,B_508)))
      | ~ v1_funct_2(F_506,D_505,B_508)
      | ~ v1_funct_1(F_506)
      | ~ m1_subset_1(E_510,k1_zfmisc_1(k2_zfmisc_1(C_507,B_508)))
      | ~ v1_funct_2(E_510,C_507,B_508)
      | ~ v1_funct_1(E_510)
      | ~ m1_subset_1(D_505,k1_zfmisc_1(A_509))
      | v1_xboole_0(D_505)
      | ~ m1_subset_1(C_507,k1_zfmisc_1(A_509))
      | v1_xboole_0(C_507)
      | v1_xboole_0(B_508)
      | v1_xboole_0(A_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_4493,plain,(
    ! [A_509,C_507,E_510] :
      ( v1_funct_1(k1_tmap_1(A_509,'#skF_2',C_507,'#skF_4',E_510,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_510,k1_zfmisc_1(k2_zfmisc_1(C_507,'#skF_2')))
      | ~ v1_funct_2(E_510,C_507,'#skF_2')
      | ~ v1_funct_1(E_510)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_509))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_507,k1_zfmisc_1(A_509))
      | v1_xboole_0(C_507)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_509) ) ),
    inference(resolution,[status(thm)],[c_50,c_4489])).

tff(c_4500,plain,(
    ! [A_509,C_507,E_510] :
      ( v1_funct_1(k1_tmap_1(A_509,'#skF_2',C_507,'#skF_4',E_510,'#skF_6'))
      | ~ m1_subset_1(E_510,k1_zfmisc_1(k2_zfmisc_1(C_507,'#skF_2')))
      | ~ v1_funct_2(E_510,C_507,'#skF_2')
      | ~ v1_funct_1(E_510)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_509))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_507,k1_zfmisc_1(A_509))
      | v1_xboole_0(C_507)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_509) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4493])).

tff(c_5492,plain,(
    ! [A_561,C_562,E_563] :
      ( v1_funct_1(k1_tmap_1(A_561,'#skF_2',C_562,'#skF_4',E_563,'#skF_6'))
      | ~ m1_subset_1(E_563,k1_zfmisc_1(k2_zfmisc_1(C_562,'#skF_2')))
      | ~ v1_funct_2(E_563,C_562,'#skF_2')
      | ~ v1_funct_1(E_563)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_561))
      | ~ m1_subset_1(C_562,k1_zfmisc_1(A_561))
      | v1_xboole_0(C_562)
      | v1_xboole_0(A_561) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_4500])).

tff(c_5497,plain,(
    ! [A_561] :
      ( v1_funct_1(k1_tmap_1(A_561,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_561))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_561))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_561) ) ),
    inference(resolution,[status(thm)],[c_56,c_5492])).

tff(c_5505,plain,(
    ! [A_561] :
      ( v1_funct_1(k1_tmap_1(A_561,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_561))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_561))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_561) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5497])).

tff(c_6482,plain,(
    ! [A_597] :
      ( v1_funct_1(k1_tmap_1(A_597,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_597))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_597))
      | v1_xboole_0(A_597) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_5505])).

tff(c_6485,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_6482])).

tff(c_6488,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6485])).

tff(c_6489,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_6488])).

tff(c_3844,plain,(
    ! [A_478,B_479,C_480,D_481] :
      ( k2_partfun1(A_478,B_479,C_480,D_481) = k7_relat_1(C_480,D_481)
      | ~ m1_subset_1(C_480,k1_zfmisc_1(k2_zfmisc_1(A_478,B_479)))
      | ~ v1_funct_1(C_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3846,plain,(
    ! [D_481] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_481) = k7_relat_1('#skF_5',D_481)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_3844])).

tff(c_3851,plain,(
    ! [D_481] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_481) = k7_relat_1('#skF_5',D_481) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3846])).

tff(c_3848,plain,(
    ! [D_481] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_481) = k7_relat_1('#skF_6',D_481)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_3844])).

tff(c_3854,plain,(
    ! [D_481] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_481) = k7_relat_1('#skF_6',D_481) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3848])).

tff(c_5155,plain,(
    ! [C_546,E_550,B_548,A_549,D_547,F_551] :
      ( k2_partfun1(k4_subset_1(A_549,C_546,D_547),B_548,k1_tmap_1(A_549,B_548,C_546,D_547,E_550,F_551),D_547) = F_551
      | ~ m1_subset_1(k1_tmap_1(A_549,B_548,C_546,D_547,E_550,F_551),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_549,C_546,D_547),B_548)))
      | ~ v1_funct_2(k1_tmap_1(A_549,B_548,C_546,D_547,E_550,F_551),k4_subset_1(A_549,C_546,D_547),B_548)
      | ~ v1_funct_1(k1_tmap_1(A_549,B_548,C_546,D_547,E_550,F_551))
      | k2_partfun1(D_547,B_548,F_551,k9_subset_1(A_549,C_546,D_547)) != k2_partfun1(C_546,B_548,E_550,k9_subset_1(A_549,C_546,D_547))
      | ~ m1_subset_1(F_551,k1_zfmisc_1(k2_zfmisc_1(D_547,B_548)))
      | ~ v1_funct_2(F_551,D_547,B_548)
      | ~ v1_funct_1(F_551)
      | ~ m1_subset_1(E_550,k1_zfmisc_1(k2_zfmisc_1(C_546,B_548)))
      | ~ v1_funct_2(E_550,C_546,B_548)
      | ~ v1_funct_1(E_550)
      | ~ m1_subset_1(D_547,k1_zfmisc_1(A_549))
      | v1_xboole_0(D_547)
      | ~ m1_subset_1(C_546,k1_zfmisc_1(A_549))
      | v1_xboole_0(C_546)
      | v1_xboole_0(B_548)
      | v1_xboole_0(A_549) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_14351,plain,(
    ! [B_810,D_807,E_812,C_809,F_808,A_811] :
      ( k2_partfun1(k4_subset_1(A_811,C_809,D_807),B_810,k1_tmap_1(A_811,B_810,C_809,D_807,E_812,F_808),D_807) = F_808
      | ~ v1_funct_2(k1_tmap_1(A_811,B_810,C_809,D_807,E_812,F_808),k4_subset_1(A_811,C_809,D_807),B_810)
      | ~ v1_funct_1(k1_tmap_1(A_811,B_810,C_809,D_807,E_812,F_808))
      | k2_partfun1(D_807,B_810,F_808,k9_subset_1(A_811,C_809,D_807)) != k2_partfun1(C_809,B_810,E_812,k9_subset_1(A_811,C_809,D_807))
      | ~ m1_subset_1(F_808,k1_zfmisc_1(k2_zfmisc_1(D_807,B_810)))
      | ~ v1_funct_2(F_808,D_807,B_810)
      | ~ v1_funct_1(F_808)
      | ~ m1_subset_1(E_812,k1_zfmisc_1(k2_zfmisc_1(C_809,B_810)))
      | ~ v1_funct_2(E_812,C_809,B_810)
      | ~ v1_funct_1(E_812)
      | ~ m1_subset_1(D_807,k1_zfmisc_1(A_811))
      | v1_xboole_0(D_807)
      | ~ m1_subset_1(C_809,k1_zfmisc_1(A_811))
      | v1_xboole_0(C_809)
      | v1_xboole_0(B_810)
      | v1_xboole_0(A_811) ) ),
    inference(resolution,[status(thm)],[c_42,c_5155])).

tff(c_15968,plain,(
    ! [F_860,B_862,E_864,D_859,C_861,A_863] :
      ( k2_partfun1(k4_subset_1(A_863,C_861,D_859),B_862,k1_tmap_1(A_863,B_862,C_861,D_859,E_864,F_860),D_859) = F_860
      | ~ v1_funct_1(k1_tmap_1(A_863,B_862,C_861,D_859,E_864,F_860))
      | k2_partfun1(D_859,B_862,F_860,k9_subset_1(A_863,C_861,D_859)) != k2_partfun1(C_861,B_862,E_864,k9_subset_1(A_863,C_861,D_859))
      | ~ m1_subset_1(F_860,k1_zfmisc_1(k2_zfmisc_1(D_859,B_862)))
      | ~ v1_funct_2(F_860,D_859,B_862)
      | ~ v1_funct_1(F_860)
      | ~ m1_subset_1(E_864,k1_zfmisc_1(k2_zfmisc_1(C_861,B_862)))
      | ~ v1_funct_2(E_864,C_861,B_862)
      | ~ v1_funct_1(E_864)
      | ~ m1_subset_1(D_859,k1_zfmisc_1(A_863))
      | v1_xboole_0(D_859)
      | ~ m1_subset_1(C_861,k1_zfmisc_1(A_863))
      | v1_xboole_0(C_861)
      | v1_xboole_0(B_862)
      | v1_xboole_0(A_863) ) ),
    inference(resolution,[status(thm)],[c_44,c_14351])).

tff(c_15974,plain,(
    ! [A_863,C_861,E_864] :
      ( k2_partfun1(k4_subset_1(A_863,C_861,'#skF_4'),'#skF_2',k1_tmap_1(A_863,'#skF_2',C_861,'#skF_4',E_864,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_863,'#skF_2',C_861,'#skF_4',E_864,'#skF_6'))
      | k2_partfun1(C_861,'#skF_2',E_864,k9_subset_1(A_863,C_861,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_863,C_861,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_864,k1_zfmisc_1(k2_zfmisc_1(C_861,'#skF_2')))
      | ~ v1_funct_2(E_864,C_861,'#skF_2')
      | ~ v1_funct_1(E_864)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_863))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_861,k1_zfmisc_1(A_863))
      | v1_xboole_0(C_861)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_863) ) ),
    inference(resolution,[status(thm)],[c_50,c_15968])).

tff(c_15982,plain,(
    ! [A_863,C_861,E_864] :
      ( k2_partfun1(k4_subset_1(A_863,C_861,'#skF_4'),'#skF_2',k1_tmap_1(A_863,'#skF_2',C_861,'#skF_4',E_864,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_863,'#skF_2',C_861,'#skF_4',E_864,'#skF_6'))
      | k2_partfun1(C_861,'#skF_2',E_864,k9_subset_1(A_863,C_861,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_863,C_861,'#skF_4'))
      | ~ m1_subset_1(E_864,k1_zfmisc_1(k2_zfmisc_1(C_861,'#skF_2')))
      | ~ v1_funct_2(E_864,C_861,'#skF_2')
      | ~ v1_funct_1(E_864)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_863))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_861,k1_zfmisc_1(A_863))
      | v1_xboole_0(C_861)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_863) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3854,c_15974])).

tff(c_20152,plain,(
    ! [A_950,C_951,E_952] :
      ( k2_partfun1(k4_subset_1(A_950,C_951,'#skF_4'),'#skF_2',k1_tmap_1(A_950,'#skF_2',C_951,'#skF_4',E_952,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_950,'#skF_2',C_951,'#skF_4',E_952,'#skF_6'))
      | k2_partfun1(C_951,'#skF_2',E_952,k9_subset_1(A_950,C_951,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_950,C_951,'#skF_4'))
      | ~ m1_subset_1(E_952,k1_zfmisc_1(k2_zfmisc_1(C_951,'#skF_2')))
      | ~ v1_funct_2(E_952,C_951,'#skF_2')
      | ~ v1_funct_1(E_952)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_950))
      | ~ m1_subset_1(C_951,k1_zfmisc_1(A_950))
      | v1_xboole_0(C_951)
      | v1_xboole_0(A_950) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_15982])).

tff(c_20157,plain,(
    ! [A_950] :
      ( k2_partfun1(k4_subset_1(A_950,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_950,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_950,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_950,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_950,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_950))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_950))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_950) ) ),
    inference(resolution,[status(thm)],[c_56,c_20152])).

tff(c_20165,plain,(
    ! [A_950] :
      ( k2_partfun1(k4_subset_1(A_950,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_950,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_950,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_950,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_950,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_950))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_950))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_950) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3851,c_20157])).

tff(c_23690,plain,(
    ! [A_992] :
      ( k2_partfun1(k4_subset_1(A_992,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_992,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_992,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_992,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_992,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_992))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_992))
      | v1_xboole_0(A_992) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_20165])).

tff(c_166,plain,(
    ! [C_230,A_231,B_232] :
      ( v1_relat_1(C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_174,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_166])).

tff(c_205,plain,(
    ! [C_238,A_239,B_240] :
      ( v4_relat_1(C_238,A_239)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_213,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_205])).

tff(c_280,plain,(
    ! [B_256,A_257] :
      ( k1_relat_1(B_256) = A_257
      | ~ v1_partfun1(B_256,A_257)
      | ~ v4_relat_1(B_256,A_257)
      | ~ v1_relat_1(B_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_283,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_213,c_280])).

tff(c_289,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_283])).

tff(c_293,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_289])).

tff(c_937,plain,(
    ! [C_301,A_302,B_303] :
      ( v1_partfun1(C_301,A_302)
      | ~ v1_funct_2(C_301,A_302,B_303)
      | ~ v1_funct_1(C_301)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_302,B_303)))
      | v1_xboole_0(B_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_943,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_937])).

tff(c_950,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_943])).

tff(c_952,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_293,c_950])).

tff(c_953,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_958,plain,(
    ! [B_15] :
      ( k7_relat_1('#skF_6',B_15) = k1_xboole_0
      | ~ r1_xboole_0(B_15,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_953,c_12])).

tff(c_1438,plain,(
    ! [B_330] :
      ( k7_relat_1('#skF_6',B_330) = k1_xboole_0
      | ~ r1_xboole_0(B_330,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_958])).

tff(c_1442,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_6',A_16) = k1_xboole_0
      | ~ r1_subset_1(A_16,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_16,c_1438])).

tff(c_1457,plain,(
    ! [A_332] :
      ( k7_relat_1('#skF_6',A_332) = k1_xboole_0
      | ~ r1_subset_1(A_332,'#skF_4')
      | v1_xboole_0(A_332) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1442])).

tff(c_1460,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1457])).

tff(c_1463,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1460])).

tff(c_10,plain,(
    ! [C_12,A_10,B_11] :
      ( k3_xboole_0(k7_relat_1(C_12,A_10),k7_relat_1(C_12,B_11)) = k7_relat_1(C_12,k3_xboole_0(A_10,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1501,plain,(
    ! [A_10] :
      ( k7_relat_1('#skF_6',k3_xboole_0(A_10,'#skF_3')) = k3_xboole_0(k7_relat_1('#skF_6',A_10),k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1463,c_10])).

tff(c_1507,plain,(
    ! [A_10] : k7_relat_1('#skF_6',k3_xboole_0(A_10,'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_98,c_2,c_1501])).

tff(c_1673,plain,(
    ! [A_340,B_341,C_342,D_343] :
      ( k2_partfun1(A_340,B_341,C_342,D_343) = k7_relat_1(C_342,D_343)
      | ~ m1_subset_1(C_342,k1_zfmisc_1(k2_zfmisc_1(A_340,B_341)))
      | ~ v1_funct_1(C_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1677,plain,(
    ! [D_343] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_343) = k7_relat_1('#skF_6',D_343)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_1673])).

tff(c_1683,plain,(
    ! [D_343] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_343) = k7_relat_1('#skF_6',D_343) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1677])).

tff(c_173,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_166])).

tff(c_214,plain,(
    ! [B_241,A_242] :
      ( r1_subset_1(B_241,A_242)
      | ~ r1_subset_1(A_242,B_241)
      | v1_xboole_0(B_241)
      | v1_xboole_0(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_216,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_214])).

tff(c_219,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_216])).

tff(c_212,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_205])).

tff(c_286,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_212,c_280])).

tff(c_292,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_286])).

tff(c_979,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_292])).

tff(c_1401,plain,(
    ! [C_326,A_327,B_328] :
      ( v1_partfun1(C_326,A_327)
      | ~ v1_funct_2(C_326,A_327,B_328)
      | ~ v1_funct_1(C_326)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(A_327,B_328)))
      | v1_xboole_0(B_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1404,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1401])).

tff(c_1410,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1404])).

tff(c_1412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_979,c_1410])).

tff(c_1413,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_292])).

tff(c_1418,plain,(
    ! [B_15] :
      ( k7_relat_1('#skF_5',B_15) = k1_xboole_0
      | ~ r1_xboole_0(B_15,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1413,c_12])).

tff(c_1430,plain,(
    ! [B_329] :
      ( k7_relat_1('#skF_5',B_329) = k1_xboole_0
      | ~ r1_xboole_0(B_329,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_1418])).

tff(c_1434,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_5',A_16) = k1_xboole_0
      | ~ r1_subset_1(A_16,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_16,c_1430])).

tff(c_1446,plain,(
    ! [A_331] :
      ( k7_relat_1('#skF_5',A_331) = k1_xboole_0
      | ~ r1_subset_1(A_331,'#skF_3')
      | v1_xboole_0(A_331) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1434])).

tff(c_1449,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_219,c_1446])).

tff(c_1452,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1449])).

tff(c_1464,plain,(
    ! [C_333,A_334,B_335] :
      ( k3_xboole_0(k7_relat_1(C_333,A_334),k7_relat_1(C_333,B_335)) = k7_relat_1(C_333,k3_xboole_0(A_334,B_335))
      | ~ v1_relat_1(C_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1479,plain,(
    ! [B_335] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_4',B_335)) = k3_xboole_0(k1_xboole_0,k7_relat_1('#skF_5',B_335))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1452,c_1464])).

tff(c_1492,plain,(
    ! [B_335] : k7_relat_1('#skF_5',k3_xboole_0('#skF_4',B_335)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_98,c_1479])).

tff(c_1675,plain,(
    ! [D_343] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_343) = k7_relat_1('#skF_5',D_343)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_1673])).

tff(c_1680,plain,(
    ! [D_343] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_343) = k7_relat_1('#skF_5',D_343) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1675])).

tff(c_238,plain,(
    ! [A_250,B_251,C_252] :
      ( k9_subset_1(A_250,B_251,C_252) = k3_xboole_0(B_251,C_252)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(A_250)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_250,plain,(
    ! [B_251] : k9_subset_1('#skF_1',B_251,'#skF_4') = k3_xboole_0(B_251,'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_238])).

tff(c_48,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_165,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_260,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_250,c_165])).

tff(c_261,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_4','#skF_3')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_260])).

tff(c_1686,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_4','#skF_3')) != k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1680,c_261])).

tff(c_1687,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_4','#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1492,c_1686])).

tff(c_1707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_1683,c_1687])).

tff(c_1708,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3041,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1708])).

tff(c_23701,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_23690,c_3041])).

tff(c_23715,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_3769,c_3771,c_2,c_3690,c_2,c_3690,c_6489,c_23701])).

tff(c_23717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_23715])).

tff(c_23718,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1708])).

tff(c_46170,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_46158,c_23718])).

tff(c_46184,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_24448,c_24371,c_24454,c_24371,c_26310,c_46170])).

tff(c_46186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_46184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.39/5.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.39/5.87  
% 13.39/5.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.39/5.87  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.39/5.87  
% 13.39/5.87  %Foreground sorts:
% 13.39/5.87  
% 13.39/5.87  
% 13.39/5.87  %Background operators:
% 13.39/5.87  
% 13.39/5.87  
% 13.39/5.87  %Foreground operators:
% 13.39/5.87  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 13.39/5.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.39/5.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.39/5.87  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 13.39/5.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.39/5.87  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 13.39/5.87  tff('#skF_5', type, '#skF_5': $i).
% 13.39/5.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.39/5.87  tff('#skF_6', type, '#skF_6': $i).
% 13.39/5.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.39/5.87  tff('#skF_2', type, '#skF_2': $i).
% 13.39/5.87  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 13.39/5.87  tff('#skF_3', type, '#skF_3': $i).
% 13.39/5.87  tff('#skF_1', type, '#skF_1': $i).
% 13.39/5.87  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.39/5.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.39/5.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.39/5.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.39/5.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.39/5.87  tff('#skF_4', type, '#skF_4': $i).
% 13.39/5.87  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.39/5.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.39/5.87  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 13.39/5.87  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.39/5.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.39/5.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.39/5.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.39/5.87  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 13.39/5.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.39/5.87  
% 13.80/5.91  tff(f_233, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 13.80/5.91  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.80/5.91  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.80/5.91  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 13.80/5.91  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 13.80/5.91  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.80/5.91  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 13.80/5.91  tff(f_95, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 13.80/5.91  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 13.80/5.91  tff(f_44, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_relat_1)).
% 13.80/5.91  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 13.80/5.91  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) => r1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_subset_1)).
% 13.80/5.91  tff(f_191, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 13.80/5.91  tff(f_109, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 13.80/5.91  tff(f_157, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 13.80/5.91  tff(c_74, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_233])).
% 13.80/5.91  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_233])).
% 13.80/5.91  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_233])).
% 13.80/5.91  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_233])).
% 13.80/5.91  tff(c_1710, plain, (![C_346, A_347, B_348]: (v1_relat_1(C_346) | ~m1_subset_1(C_346, k1_zfmisc_1(k2_zfmisc_1(A_347, B_348))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.80/5.91  tff(c_1718, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_1710])).
% 13.80/5.91  tff(c_82, plain, (![B_227, A_228]: (k3_xboole_0(B_227, A_228)=k3_xboole_0(A_228, B_227))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.80/5.91  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.80/5.91  tff(c_98, plain, (![A_228]: (k3_xboole_0(k1_xboole_0, A_228)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_82, c_4])).
% 13.80/5.91  tff(c_70, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_233])).
% 13.80/5.91  tff(c_62, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_233])).
% 13.80/5.91  tff(c_66, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_233])).
% 13.80/5.91  tff(c_16, plain, (![A_16, B_17]: (r1_xboole_0(A_16, B_17) | ~r1_subset_1(A_16, B_17) | v1_xboole_0(B_17) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.80/5.91  tff(c_72, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_233])).
% 13.80/5.91  tff(c_1749, plain, (![C_354, A_355, B_356]: (v4_relat_1(C_354, A_355) | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(A_355, B_356))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.80/5.91  tff(c_1757, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1749])).
% 13.80/5.91  tff(c_1786, plain, (![B_366, A_367]: (k1_relat_1(B_366)=A_367 | ~v1_partfun1(B_366, A_367) | ~v4_relat_1(B_366, A_367) | ~v1_relat_1(B_366))), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.80/5.91  tff(c_1789, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1757, c_1786])).
% 13.80/5.91  tff(c_1795, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1718, c_1789])).
% 13.80/5.91  tff(c_1799, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_1795])).
% 13.80/5.91  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_233])).
% 13.80/5.91  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_233])).
% 13.80/5.91  tff(c_3008, plain, (![C_426, A_427, B_428]: (v1_partfun1(C_426, A_427) | ~v1_funct_2(C_426, A_427, B_428) | ~v1_funct_1(C_426) | ~m1_subset_1(C_426, k1_zfmisc_1(k2_zfmisc_1(A_427, B_428))) | v1_xboole_0(B_428))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.80/5.91  tff(c_3014, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_3008])).
% 13.80/5.91  tff(c_3021, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3014])).
% 13.80/5.91  tff(c_3023, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1799, c_3021])).
% 13.80/5.91  tff(c_3024, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_1795])).
% 13.80/5.91  tff(c_12, plain, (![A_13, B_15]: (k7_relat_1(A_13, B_15)=k1_xboole_0 | ~r1_xboole_0(B_15, k1_relat_1(A_13)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.80/5.91  tff(c_3032, plain, (![B_15]: (k7_relat_1('#skF_6', B_15)=k1_xboole_0 | ~r1_xboole_0(B_15, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3024, c_12])).
% 13.80/5.91  tff(c_24333, plain, (![B_1027]: (k7_relat_1('#skF_6', B_1027)=k1_xboole_0 | ~r1_xboole_0(B_1027, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1718, c_3032])).
% 13.80/5.91  tff(c_24337, plain, (![A_16]: (k7_relat_1('#skF_6', A_16)=k1_xboole_0 | ~r1_subset_1(A_16, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_16, c_24333])).
% 13.80/5.91  tff(c_24352, plain, (![A_1029]: (k7_relat_1('#skF_6', A_1029)=k1_xboole_0 | ~r1_subset_1(A_1029, '#skF_4') | v1_xboole_0(A_1029))), inference(negUnitSimplification, [status(thm)], [c_66, c_24337])).
% 13.80/5.91  tff(c_24355, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_24352])).
% 13.80/5.91  tff(c_24358, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_24355])).
% 13.80/5.91  tff(c_24414, plain, (![C_1037, A_1038, B_1039]: (k3_xboole_0(k7_relat_1(C_1037, A_1038), k7_relat_1(C_1037, B_1039))=k7_relat_1(C_1037, k3_xboole_0(A_1038, B_1039)) | ~v1_relat_1(C_1037))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.80/5.91  tff(c_24429, plain, (![B_1039]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_1039))=k3_xboole_0(k1_xboole_0, k7_relat_1('#skF_6', B_1039)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_24358, c_24414])).
% 13.80/5.91  tff(c_24448, plain, (![B_1039]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_1039))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1718, c_98, c_24429])).
% 13.80/5.91  tff(c_24359, plain, (![A_1030, B_1031, C_1032]: (k9_subset_1(A_1030, B_1031, C_1032)=k3_xboole_0(B_1031, C_1032) | ~m1_subset_1(C_1032, k1_zfmisc_1(A_1030)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.80/5.91  tff(c_24371, plain, (![B_1031]: (k9_subset_1('#skF_1', B_1031, '#skF_4')=k3_xboole_0(B_1031, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_24359])).
% 13.80/5.91  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_233])).
% 13.80/5.91  tff(c_1717, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_1710])).
% 13.80/5.91  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.80/5.91  tff(c_1759, plain, (![B_359, A_360]: (r1_subset_1(B_359, A_360) | ~r1_subset_1(A_360, B_359) | v1_xboole_0(B_359) | v1_xboole_0(A_360))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.80/5.91  tff(c_1761, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1759])).
% 13.80/5.91  tff(c_1764, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_1761])).
% 13.80/5.91  tff(c_1756, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_1749])).
% 13.80/5.91  tff(c_1792, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1756, c_1786])).
% 13.80/5.91  tff(c_1798, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1717, c_1792])).
% 13.80/5.91  tff(c_23720, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_1798])).
% 13.80/5.91  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_233])).
% 13.80/5.91  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_233])).
% 13.80/5.91  tff(c_24292, plain, (![C_1023, A_1024, B_1025]: (v1_partfun1(C_1023, A_1024) | ~v1_funct_2(C_1023, A_1024, B_1025) | ~v1_funct_1(C_1023) | ~m1_subset_1(C_1023, k1_zfmisc_1(k2_zfmisc_1(A_1024, B_1025))) | v1_xboole_0(B_1025))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.80/5.91  tff(c_24295, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_24292])).
% 13.80/5.91  tff(c_24301, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_24295])).
% 13.80/5.91  tff(c_24303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_23720, c_24301])).
% 13.80/5.91  tff(c_24304, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_1798])).
% 13.80/5.91  tff(c_24312, plain, (![B_15]: (k7_relat_1('#skF_5', B_15)=k1_xboole_0 | ~r1_xboole_0(B_15, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_24304, c_12])).
% 13.80/5.91  tff(c_24325, plain, (![B_1026]: (k7_relat_1('#skF_5', B_1026)=k1_xboole_0 | ~r1_xboole_0(B_1026, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1717, c_24312])).
% 13.80/5.91  tff(c_24329, plain, (![A_16]: (k7_relat_1('#skF_5', A_16)=k1_xboole_0 | ~r1_subset_1(A_16, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_16, c_24325])).
% 13.80/5.91  tff(c_24341, plain, (![A_1028]: (k7_relat_1('#skF_5', A_1028)=k1_xboole_0 | ~r1_subset_1(A_1028, '#skF_3') | v1_xboole_0(A_1028))), inference(negUnitSimplification, [status(thm)], [c_70, c_24329])).
% 13.80/5.91  tff(c_24344, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1764, c_24341])).
% 13.80/5.91  tff(c_24347, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_24344])).
% 13.80/5.91  tff(c_24438, plain, (![A_1038]: (k7_relat_1('#skF_5', k3_xboole_0(A_1038, '#skF_4'))=k3_xboole_0(k7_relat_1('#skF_5', A_1038), k1_xboole_0) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_24347, c_24414])).
% 13.80/5.91  tff(c_24454, plain, (![A_1038]: (k7_relat_1('#skF_5', k3_xboole_0(A_1038, '#skF_4'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1717, c_98, c_2, c_24438])).
% 13.80/5.91  tff(c_25195, plain, (![A_1073, F_1070, B_1072, D_1069, E_1074, C_1071]: (v1_funct_1(k1_tmap_1(A_1073, B_1072, C_1071, D_1069, E_1074, F_1070)) | ~m1_subset_1(F_1070, k1_zfmisc_1(k2_zfmisc_1(D_1069, B_1072))) | ~v1_funct_2(F_1070, D_1069, B_1072) | ~v1_funct_1(F_1070) | ~m1_subset_1(E_1074, k1_zfmisc_1(k2_zfmisc_1(C_1071, B_1072))) | ~v1_funct_2(E_1074, C_1071, B_1072) | ~v1_funct_1(E_1074) | ~m1_subset_1(D_1069, k1_zfmisc_1(A_1073)) | v1_xboole_0(D_1069) | ~m1_subset_1(C_1071, k1_zfmisc_1(A_1073)) | v1_xboole_0(C_1071) | v1_xboole_0(B_1072) | v1_xboole_0(A_1073))), inference(cnfTransformation, [status(thm)], [f_191])).
% 13.80/5.91  tff(c_25199, plain, (![A_1073, C_1071, E_1074]: (v1_funct_1(k1_tmap_1(A_1073, '#skF_2', C_1071, '#skF_4', E_1074, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1074, k1_zfmisc_1(k2_zfmisc_1(C_1071, '#skF_2'))) | ~v1_funct_2(E_1074, C_1071, '#skF_2') | ~v1_funct_1(E_1074) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1073)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1071, k1_zfmisc_1(A_1073)) | v1_xboole_0(C_1071) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1073))), inference(resolution, [status(thm)], [c_50, c_25195])).
% 13.80/5.91  tff(c_25206, plain, (![A_1073, C_1071, E_1074]: (v1_funct_1(k1_tmap_1(A_1073, '#skF_2', C_1071, '#skF_4', E_1074, '#skF_6')) | ~m1_subset_1(E_1074, k1_zfmisc_1(k2_zfmisc_1(C_1071, '#skF_2'))) | ~v1_funct_2(E_1074, C_1071, '#skF_2') | ~v1_funct_1(E_1074) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1073)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1071, k1_zfmisc_1(A_1073)) | v1_xboole_0(C_1071) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1073))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_25199])).
% 13.80/5.91  tff(c_25211, plain, (![A_1075, C_1076, E_1077]: (v1_funct_1(k1_tmap_1(A_1075, '#skF_2', C_1076, '#skF_4', E_1077, '#skF_6')) | ~m1_subset_1(E_1077, k1_zfmisc_1(k2_zfmisc_1(C_1076, '#skF_2'))) | ~v1_funct_2(E_1077, C_1076, '#skF_2') | ~v1_funct_1(E_1077) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1075)) | ~m1_subset_1(C_1076, k1_zfmisc_1(A_1075)) | v1_xboole_0(C_1076) | v1_xboole_0(A_1075))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_25206])).
% 13.80/5.91  tff(c_25213, plain, (![A_1075]: (v1_funct_1(k1_tmap_1(A_1075, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1075)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1075)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1075))), inference(resolution, [status(thm)], [c_56, c_25211])).
% 13.80/5.91  tff(c_25218, plain, (![A_1075]: (v1_funct_1(k1_tmap_1(A_1075, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1075)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1075)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1075))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_25213])).
% 13.80/5.91  tff(c_26303, plain, (![A_1121]: (v1_funct_1(k1_tmap_1(A_1121, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1121)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1121)) | v1_xboole_0(A_1121))), inference(negUnitSimplification, [status(thm)], [c_70, c_25218])).
% 13.80/5.91  tff(c_26306, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_26303])).
% 13.80/5.91  tff(c_26309, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_26306])).
% 13.80/5.91  tff(c_26310, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_26309])).
% 13.80/5.91  tff(c_24674, plain, (![A_1046, B_1047, C_1048, D_1049]: (k2_partfun1(A_1046, B_1047, C_1048, D_1049)=k7_relat_1(C_1048, D_1049) | ~m1_subset_1(C_1048, k1_zfmisc_1(k2_zfmisc_1(A_1046, B_1047))) | ~v1_funct_1(C_1048))), inference(cnfTransformation, [status(thm)], [f_109])).
% 13.80/5.91  tff(c_24676, plain, (![D_1049]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1049)=k7_relat_1('#skF_5', D_1049) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_24674])).
% 13.80/5.91  tff(c_24681, plain, (![D_1049]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1049)=k7_relat_1('#skF_5', D_1049))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_24676])).
% 13.80/5.91  tff(c_24678, plain, (![D_1049]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1049)=k7_relat_1('#skF_6', D_1049) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_24674])).
% 13.80/5.91  tff(c_24684, plain, (![D_1049]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1049)=k7_relat_1('#skF_6', D_1049))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_24678])).
% 13.80/5.91  tff(c_44, plain, (![A_163, C_165, D_166, F_168, B_164, E_167]: (v1_funct_2(k1_tmap_1(A_163, B_164, C_165, D_166, E_167, F_168), k4_subset_1(A_163, C_165, D_166), B_164) | ~m1_subset_1(F_168, k1_zfmisc_1(k2_zfmisc_1(D_166, B_164))) | ~v1_funct_2(F_168, D_166, B_164) | ~v1_funct_1(F_168) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(C_165, B_164))) | ~v1_funct_2(E_167, C_165, B_164) | ~v1_funct_1(E_167) | ~m1_subset_1(D_166, k1_zfmisc_1(A_163)) | v1_xboole_0(D_166) | ~m1_subset_1(C_165, k1_zfmisc_1(A_163)) | v1_xboole_0(C_165) | v1_xboole_0(B_164) | v1_xboole_0(A_163))), inference(cnfTransformation, [status(thm)], [f_191])).
% 13.80/5.91  tff(c_42, plain, (![A_163, C_165, D_166, F_168, B_164, E_167]: (m1_subset_1(k1_tmap_1(A_163, B_164, C_165, D_166, E_167, F_168), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_163, C_165, D_166), B_164))) | ~m1_subset_1(F_168, k1_zfmisc_1(k2_zfmisc_1(D_166, B_164))) | ~v1_funct_2(F_168, D_166, B_164) | ~v1_funct_1(F_168) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(C_165, B_164))) | ~v1_funct_2(E_167, C_165, B_164) | ~v1_funct_1(E_167) | ~m1_subset_1(D_166, k1_zfmisc_1(A_163)) | v1_xboole_0(D_166) | ~m1_subset_1(C_165, k1_zfmisc_1(A_163)) | v1_xboole_0(C_165) | v1_xboole_0(B_164) | v1_xboole_0(A_163))), inference(cnfTransformation, [status(thm)], [f_191])).
% 13.80/5.91  tff(c_27166, plain, (![D_1150, B_1151, F_1154, A_1152, E_1153, C_1149]: (k2_partfun1(k4_subset_1(A_1152, C_1149, D_1150), B_1151, k1_tmap_1(A_1152, B_1151, C_1149, D_1150, E_1153, F_1154), C_1149)=E_1153 | ~m1_subset_1(k1_tmap_1(A_1152, B_1151, C_1149, D_1150, E_1153, F_1154), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1152, C_1149, D_1150), B_1151))) | ~v1_funct_2(k1_tmap_1(A_1152, B_1151, C_1149, D_1150, E_1153, F_1154), k4_subset_1(A_1152, C_1149, D_1150), B_1151) | ~v1_funct_1(k1_tmap_1(A_1152, B_1151, C_1149, D_1150, E_1153, F_1154)) | k2_partfun1(D_1150, B_1151, F_1154, k9_subset_1(A_1152, C_1149, D_1150))!=k2_partfun1(C_1149, B_1151, E_1153, k9_subset_1(A_1152, C_1149, D_1150)) | ~m1_subset_1(F_1154, k1_zfmisc_1(k2_zfmisc_1(D_1150, B_1151))) | ~v1_funct_2(F_1154, D_1150, B_1151) | ~v1_funct_1(F_1154) | ~m1_subset_1(E_1153, k1_zfmisc_1(k2_zfmisc_1(C_1149, B_1151))) | ~v1_funct_2(E_1153, C_1149, B_1151) | ~v1_funct_1(E_1153) | ~m1_subset_1(D_1150, k1_zfmisc_1(A_1152)) | v1_xboole_0(D_1150) | ~m1_subset_1(C_1149, k1_zfmisc_1(A_1152)) | v1_xboole_0(C_1149) | v1_xboole_0(B_1151) | v1_xboole_0(A_1152))), inference(cnfTransformation, [status(thm)], [f_157])).
% 13.80/5.91  tff(c_44325, plain, (![D_1643, B_1646, E_1648, A_1647, C_1645, F_1644]: (k2_partfun1(k4_subset_1(A_1647, C_1645, D_1643), B_1646, k1_tmap_1(A_1647, B_1646, C_1645, D_1643, E_1648, F_1644), C_1645)=E_1648 | ~v1_funct_2(k1_tmap_1(A_1647, B_1646, C_1645, D_1643, E_1648, F_1644), k4_subset_1(A_1647, C_1645, D_1643), B_1646) | ~v1_funct_1(k1_tmap_1(A_1647, B_1646, C_1645, D_1643, E_1648, F_1644)) | k2_partfun1(D_1643, B_1646, F_1644, k9_subset_1(A_1647, C_1645, D_1643))!=k2_partfun1(C_1645, B_1646, E_1648, k9_subset_1(A_1647, C_1645, D_1643)) | ~m1_subset_1(F_1644, k1_zfmisc_1(k2_zfmisc_1(D_1643, B_1646))) | ~v1_funct_2(F_1644, D_1643, B_1646) | ~v1_funct_1(F_1644) | ~m1_subset_1(E_1648, k1_zfmisc_1(k2_zfmisc_1(C_1645, B_1646))) | ~v1_funct_2(E_1648, C_1645, B_1646) | ~v1_funct_1(E_1648) | ~m1_subset_1(D_1643, k1_zfmisc_1(A_1647)) | v1_xboole_0(D_1643) | ~m1_subset_1(C_1645, k1_zfmisc_1(A_1647)) | v1_xboole_0(C_1645) | v1_xboole_0(B_1646) | v1_xboole_0(A_1647))), inference(resolution, [status(thm)], [c_42, c_27166])).
% 13.80/5.91  tff(c_46025, plain, (![C_1706, F_1705, E_1709, A_1708, D_1704, B_1707]: (k2_partfun1(k4_subset_1(A_1708, C_1706, D_1704), B_1707, k1_tmap_1(A_1708, B_1707, C_1706, D_1704, E_1709, F_1705), C_1706)=E_1709 | ~v1_funct_1(k1_tmap_1(A_1708, B_1707, C_1706, D_1704, E_1709, F_1705)) | k2_partfun1(D_1704, B_1707, F_1705, k9_subset_1(A_1708, C_1706, D_1704))!=k2_partfun1(C_1706, B_1707, E_1709, k9_subset_1(A_1708, C_1706, D_1704)) | ~m1_subset_1(F_1705, k1_zfmisc_1(k2_zfmisc_1(D_1704, B_1707))) | ~v1_funct_2(F_1705, D_1704, B_1707) | ~v1_funct_1(F_1705) | ~m1_subset_1(E_1709, k1_zfmisc_1(k2_zfmisc_1(C_1706, B_1707))) | ~v1_funct_2(E_1709, C_1706, B_1707) | ~v1_funct_1(E_1709) | ~m1_subset_1(D_1704, k1_zfmisc_1(A_1708)) | v1_xboole_0(D_1704) | ~m1_subset_1(C_1706, k1_zfmisc_1(A_1708)) | v1_xboole_0(C_1706) | v1_xboole_0(B_1707) | v1_xboole_0(A_1708))), inference(resolution, [status(thm)], [c_44, c_44325])).
% 13.80/5.91  tff(c_46031, plain, (![A_1708, C_1706, E_1709]: (k2_partfun1(k4_subset_1(A_1708, C_1706, '#skF_4'), '#skF_2', k1_tmap_1(A_1708, '#skF_2', C_1706, '#skF_4', E_1709, '#skF_6'), C_1706)=E_1709 | ~v1_funct_1(k1_tmap_1(A_1708, '#skF_2', C_1706, '#skF_4', E_1709, '#skF_6')) | k2_partfun1(C_1706, '#skF_2', E_1709, k9_subset_1(A_1708, C_1706, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1708, C_1706, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1709, k1_zfmisc_1(k2_zfmisc_1(C_1706, '#skF_2'))) | ~v1_funct_2(E_1709, C_1706, '#skF_2') | ~v1_funct_1(E_1709) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1708)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1706, k1_zfmisc_1(A_1708)) | v1_xboole_0(C_1706) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1708))), inference(resolution, [status(thm)], [c_50, c_46025])).
% 13.80/5.91  tff(c_46039, plain, (![A_1708, C_1706, E_1709]: (k2_partfun1(k4_subset_1(A_1708, C_1706, '#skF_4'), '#skF_2', k1_tmap_1(A_1708, '#skF_2', C_1706, '#skF_4', E_1709, '#skF_6'), C_1706)=E_1709 | ~v1_funct_1(k1_tmap_1(A_1708, '#skF_2', C_1706, '#skF_4', E_1709, '#skF_6')) | k2_partfun1(C_1706, '#skF_2', E_1709, k9_subset_1(A_1708, C_1706, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1708, C_1706, '#skF_4')) | ~m1_subset_1(E_1709, k1_zfmisc_1(k2_zfmisc_1(C_1706, '#skF_2'))) | ~v1_funct_2(E_1709, C_1706, '#skF_2') | ~v1_funct_1(E_1709) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1708)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1706, k1_zfmisc_1(A_1708)) | v1_xboole_0(C_1706) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1708))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_24684, c_46031])).
% 13.80/5.91  tff(c_46119, plain, (![A_1730, C_1731, E_1732]: (k2_partfun1(k4_subset_1(A_1730, C_1731, '#skF_4'), '#skF_2', k1_tmap_1(A_1730, '#skF_2', C_1731, '#skF_4', E_1732, '#skF_6'), C_1731)=E_1732 | ~v1_funct_1(k1_tmap_1(A_1730, '#skF_2', C_1731, '#skF_4', E_1732, '#skF_6')) | k2_partfun1(C_1731, '#skF_2', E_1732, k9_subset_1(A_1730, C_1731, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1730, C_1731, '#skF_4')) | ~m1_subset_1(E_1732, k1_zfmisc_1(k2_zfmisc_1(C_1731, '#skF_2'))) | ~v1_funct_2(E_1732, C_1731, '#skF_2') | ~v1_funct_1(E_1732) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1730)) | ~m1_subset_1(C_1731, k1_zfmisc_1(A_1730)) | v1_xboole_0(C_1731) | v1_xboole_0(A_1730))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_46039])).
% 13.80/5.91  tff(c_46124, plain, (![A_1730]: (k2_partfun1(k4_subset_1(A_1730, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1730, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1730, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1730, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1730, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1730)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1730)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1730))), inference(resolution, [status(thm)], [c_56, c_46119])).
% 13.80/5.91  tff(c_46132, plain, (![A_1730]: (k2_partfun1(k4_subset_1(A_1730, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1730, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1730, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1730, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1730, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1730)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1730)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1730))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_24681, c_46124])).
% 13.80/5.91  tff(c_46158, plain, (![A_1743]: (k2_partfun1(k4_subset_1(A_1743, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1743, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1743, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1743, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1743, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1743)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1743)) | v1_xboole_0(A_1743))), inference(negUnitSimplification, [status(thm)], [c_70, c_46132])).
% 13.80/5.91  tff(c_3652, plain, (![B_463]: (k7_relat_1('#skF_6', B_463)=k1_xboole_0 | ~r1_xboole_0(B_463, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1718, c_3032])).
% 13.80/5.91  tff(c_3656, plain, (![A_16]: (k7_relat_1('#skF_6', A_16)=k1_xboole_0 | ~r1_subset_1(A_16, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_16, c_3652])).
% 13.80/5.91  tff(c_3671, plain, (![A_465]: (k7_relat_1('#skF_6', A_465)=k1_xboole_0 | ~r1_subset_1(A_465, '#skF_4') | v1_xboole_0(A_465))), inference(negUnitSimplification, [status(thm)], [c_66, c_3656])).
% 13.80/5.91  tff(c_3674, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_3671])).
% 13.80/5.91  tff(c_3677, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_3674])).
% 13.80/5.91  tff(c_3733, plain, (![C_473, A_474, B_475]: (k3_xboole_0(k7_relat_1(C_473, A_474), k7_relat_1(C_473, B_475))=k7_relat_1(C_473, k3_xboole_0(A_474, B_475)) | ~v1_relat_1(C_473))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.80/5.91  tff(c_3751, plain, (![A_474]: (k7_relat_1('#skF_6', k3_xboole_0(A_474, '#skF_3'))=k3_xboole_0(k7_relat_1('#skF_6', A_474), k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3677, c_3733])).
% 13.80/5.91  tff(c_3769, plain, (![A_474]: (k7_relat_1('#skF_6', k3_xboole_0(A_474, '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1718, c_98, c_2, c_3751])).
% 13.80/5.91  tff(c_3042, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_1798])).
% 13.80/5.91  tff(c_3615, plain, (![C_459, A_460, B_461]: (v1_partfun1(C_459, A_460) | ~v1_funct_2(C_459, A_460, B_461) | ~v1_funct_1(C_459) | ~m1_subset_1(C_459, k1_zfmisc_1(k2_zfmisc_1(A_460, B_461))) | v1_xboole_0(B_461))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.80/5.91  tff(c_3618, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_3615])).
% 13.80/5.91  tff(c_3624, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3618])).
% 13.80/5.91  tff(c_3626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3042, c_3624])).
% 13.80/5.91  tff(c_3627, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_1798])).
% 13.80/5.91  tff(c_3635, plain, (![B_15]: (k7_relat_1('#skF_5', B_15)=k1_xboole_0 | ~r1_xboole_0(B_15, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3627, c_12])).
% 13.80/5.91  tff(c_3644, plain, (![B_462]: (k7_relat_1('#skF_5', B_462)=k1_xboole_0 | ~r1_xboole_0(B_462, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1717, c_3635])).
% 13.80/5.91  tff(c_3648, plain, (![A_16]: (k7_relat_1('#skF_5', A_16)=k1_xboole_0 | ~r1_subset_1(A_16, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_16, c_3644])).
% 13.80/5.91  tff(c_3660, plain, (![A_464]: (k7_relat_1('#skF_5', A_464)=k1_xboole_0 | ~r1_subset_1(A_464, '#skF_3') | v1_xboole_0(A_464))), inference(negUnitSimplification, [status(thm)], [c_70, c_3648])).
% 13.80/5.91  tff(c_3663, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1764, c_3660])).
% 13.80/5.91  tff(c_3666, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_3663])).
% 13.80/5.91  tff(c_3754, plain, (![B_475]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', B_475))=k3_xboole_0(k1_xboole_0, k7_relat_1('#skF_5', B_475)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3666, c_3733])).
% 13.80/5.91  tff(c_3771, plain, (![B_475]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', B_475))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1717, c_98, c_3754])).
% 13.80/5.91  tff(c_3678, plain, (![A_466, B_467, C_468]: (k9_subset_1(A_466, B_467, C_468)=k3_xboole_0(B_467, C_468) | ~m1_subset_1(C_468, k1_zfmisc_1(A_466)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.80/5.91  tff(c_3690, plain, (![B_467]: (k9_subset_1('#skF_1', B_467, '#skF_4')=k3_xboole_0(B_467, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_3678])).
% 13.80/5.91  tff(c_4489, plain, (![C_507, B_508, D_505, A_509, E_510, F_506]: (v1_funct_1(k1_tmap_1(A_509, B_508, C_507, D_505, E_510, F_506)) | ~m1_subset_1(F_506, k1_zfmisc_1(k2_zfmisc_1(D_505, B_508))) | ~v1_funct_2(F_506, D_505, B_508) | ~v1_funct_1(F_506) | ~m1_subset_1(E_510, k1_zfmisc_1(k2_zfmisc_1(C_507, B_508))) | ~v1_funct_2(E_510, C_507, B_508) | ~v1_funct_1(E_510) | ~m1_subset_1(D_505, k1_zfmisc_1(A_509)) | v1_xboole_0(D_505) | ~m1_subset_1(C_507, k1_zfmisc_1(A_509)) | v1_xboole_0(C_507) | v1_xboole_0(B_508) | v1_xboole_0(A_509))), inference(cnfTransformation, [status(thm)], [f_191])).
% 13.80/5.91  tff(c_4493, plain, (![A_509, C_507, E_510]: (v1_funct_1(k1_tmap_1(A_509, '#skF_2', C_507, '#skF_4', E_510, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_510, k1_zfmisc_1(k2_zfmisc_1(C_507, '#skF_2'))) | ~v1_funct_2(E_510, C_507, '#skF_2') | ~v1_funct_1(E_510) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_509)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_507, k1_zfmisc_1(A_509)) | v1_xboole_0(C_507) | v1_xboole_0('#skF_2') | v1_xboole_0(A_509))), inference(resolution, [status(thm)], [c_50, c_4489])).
% 13.80/5.91  tff(c_4500, plain, (![A_509, C_507, E_510]: (v1_funct_1(k1_tmap_1(A_509, '#skF_2', C_507, '#skF_4', E_510, '#skF_6')) | ~m1_subset_1(E_510, k1_zfmisc_1(k2_zfmisc_1(C_507, '#skF_2'))) | ~v1_funct_2(E_510, C_507, '#skF_2') | ~v1_funct_1(E_510) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_509)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_507, k1_zfmisc_1(A_509)) | v1_xboole_0(C_507) | v1_xboole_0('#skF_2') | v1_xboole_0(A_509))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4493])).
% 13.80/5.91  tff(c_5492, plain, (![A_561, C_562, E_563]: (v1_funct_1(k1_tmap_1(A_561, '#skF_2', C_562, '#skF_4', E_563, '#skF_6')) | ~m1_subset_1(E_563, k1_zfmisc_1(k2_zfmisc_1(C_562, '#skF_2'))) | ~v1_funct_2(E_563, C_562, '#skF_2') | ~v1_funct_1(E_563) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_561)) | ~m1_subset_1(C_562, k1_zfmisc_1(A_561)) | v1_xboole_0(C_562) | v1_xboole_0(A_561))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_4500])).
% 13.80/5.91  tff(c_5497, plain, (![A_561]: (v1_funct_1(k1_tmap_1(A_561, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_561)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_561)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_561))), inference(resolution, [status(thm)], [c_56, c_5492])).
% 13.80/5.91  tff(c_5505, plain, (![A_561]: (v1_funct_1(k1_tmap_1(A_561, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_561)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_561)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_561))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5497])).
% 13.80/5.91  tff(c_6482, plain, (![A_597]: (v1_funct_1(k1_tmap_1(A_597, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_597)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_597)) | v1_xboole_0(A_597))), inference(negUnitSimplification, [status(thm)], [c_70, c_5505])).
% 13.80/5.91  tff(c_6485, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_6482])).
% 13.80/5.91  tff(c_6488, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6485])).
% 13.80/5.91  tff(c_6489, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_6488])).
% 13.80/5.91  tff(c_3844, plain, (![A_478, B_479, C_480, D_481]: (k2_partfun1(A_478, B_479, C_480, D_481)=k7_relat_1(C_480, D_481) | ~m1_subset_1(C_480, k1_zfmisc_1(k2_zfmisc_1(A_478, B_479))) | ~v1_funct_1(C_480))), inference(cnfTransformation, [status(thm)], [f_109])).
% 13.80/5.91  tff(c_3846, plain, (![D_481]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_481)=k7_relat_1('#skF_5', D_481) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_3844])).
% 13.80/5.91  tff(c_3851, plain, (![D_481]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_481)=k7_relat_1('#skF_5', D_481))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3846])).
% 13.80/5.91  tff(c_3848, plain, (![D_481]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_481)=k7_relat_1('#skF_6', D_481) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_3844])).
% 13.80/5.91  tff(c_3854, plain, (![D_481]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_481)=k7_relat_1('#skF_6', D_481))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3848])).
% 13.80/5.91  tff(c_5155, plain, (![C_546, E_550, B_548, A_549, D_547, F_551]: (k2_partfun1(k4_subset_1(A_549, C_546, D_547), B_548, k1_tmap_1(A_549, B_548, C_546, D_547, E_550, F_551), D_547)=F_551 | ~m1_subset_1(k1_tmap_1(A_549, B_548, C_546, D_547, E_550, F_551), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_549, C_546, D_547), B_548))) | ~v1_funct_2(k1_tmap_1(A_549, B_548, C_546, D_547, E_550, F_551), k4_subset_1(A_549, C_546, D_547), B_548) | ~v1_funct_1(k1_tmap_1(A_549, B_548, C_546, D_547, E_550, F_551)) | k2_partfun1(D_547, B_548, F_551, k9_subset_1(A_549, C_546, D_547))!=k2_partfun1(C_546, B_548, E_550, k9_subset_1(A_549, C_546, D_547)) | ~m1_subset_1(F_551, k1_zfmisc_1(k2_zfmisc_1(D_547, B_548))) | ~v1_funct_2(F_551, D_547, B_548) | ~v1_funct_1(F_551) | ~m1_subset_1(E_550, k1_zfmisc_1(k2_zfmisc_1(C_546, B_548))) | ~v1_funct_2(E_550, C_546, B_548) | ~v1_funct_1(E_550) | ~m1_subset_1(D_547, k1_zfmisc_1(A_549)) | v1_xboole_0(D_547) | ~m1_subset_1(C_546, k1_zfmisc_1(A_549)) | v1_xboole_0(C_546) | v1_xboole_0(B_548) | v1_xboole_0(A_549))), inference(cnfTransformation, [status(thm)], [f_157])).
% 13.80/5.91  tff(c_14351, plain, (![B_810, D_807, E_812, C_809, F_808, A_811]: (k2_partfun1(k4_subset_1(A_811, C_809, D_807), B_810, k1_tmap_1(A_811, B_810, C_809, D_807, E_812, F_808), D_807)=F_808 | ~v1_funct_2(k1_tmap_1(A_811, B_810, C_809, D_807, E_812, F_808), k4_subset_1(A_811, C_809, D_807), B_810) | ~v1_funct_1(k1_tmap_1(A_811, B_810, C_809, D_807, E_812, F_808)) | k2_partfun1(D_807, B_810, F_808, k9_subset_1(A_811, C_809, D_807))!=k2_partfun1(C_809, B_810, E_812, k9_subset_1(A_811, C_809, D_807)) | ~m1_subset_1(F_808, k1_zfmisc_1(k2_zfmisc_1(D_807, B_810))) | ~v1_funct_2(F_808, D_807, B_810) | ~v1_funct_1(F_808) | ~m1_subset_1(E_812, k1_zfmisc_1(k2_zfmisc_1(C_809, B_810))) | ~v1_funct_2(E_812, C_809, B_810) | ~v1_funct_1(E_812) | ~m1_subset_1(D_807, k1_zfmisc_1(A_811)) | v1_xboole_0(D_807) | ~m1_subset_1(C_809, k1_zfmisc_1(A_811)) | v1_xboole_0(C_809) | v1_xboole_0(B_810) | v1_xboole_0(A_811))), inference(resolution, [status(thm)], [c_42, c_5155])).
% 13.80/5.91  tff(c_15968, plain, (![F_860, B_862, E_864, D_859, C_861, A_863]: (k2_partfun1(k4_subset_1(A_863, C_861, D_859), B_862, k1_tmap_1(A_863, B_862, C_861, D_859, E_864, F_860), D_859)=F_860 | ~v1_funct_1(k1_tmap_1(A_863, B_862, C_861, D_859, E_864, F_860)) | k2_partfun1(D_859, B_862, F_860, k9_subset_1(A_863, C_861, D_859))!=k2_partfun1(C_861, B_862, E_864, k9_subset_1(A_863, C_861, D_859)) | ~m1_subset_1(F_860, k1_zfmisc_1(k2_zfmisc_1(D_859, B_862))) | ~v1_funct_2(F_860, D_859, B_862) | ~v1_funct_1(F_860) | ~m1_subset_1(E_864, k1_zfmisc_1(k2_zfmisc_1(C_861, B_862))) | ~v1_funct_2(E_864, C_861, B_862) | ~v1_funct_1(E_864) | ~m1_subset_1(D_859, k1_zfmisc_1(A_863)) | v1_xboole_0(D_859) | ~m1_subset_1(C_861, k1_zfmisc_1(A_863)) | v1_xboole_0(C_861) | v1_xboole_0(B_862) | v1_xboole_0(A_863))), inference(resolution, [status(thm)], [c_44, c_14351])).
% 13.80/5.91  tff(c_15974, plain, (![A_863, C_861, E_864]: (k2_partfun1(k4_subset_1(A_863, C_861, '#skF_4'), '#skF_2', k1_tmap_1(A_863, '#skF_2', C_861, '#skF_4', E_864, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_863, '#skF_2', C_861, '#skF_4', E_864, '#skF_6')) | k2_partfun1(C_861, '#skF_2', E_864, k9_subset_1(A_863, C_861, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_863, C_861, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_864, k1_zfmisc_1(k2_zfmisc_1(C_861, '#skF_2'))) | ~v1_funct_2(E_864, C_861, '#skF_2') | ~v1_funct_1(E_864) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_863)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_861, k1_zfmisc_1(A_863)) | v1_xboole_0(C_861) | v1_xboole_0('#skF_2') | v1_xboole_0(A_863))), inference(resolution, [status(thm)], [c_50, c_15968])).
% 13.80/5.91  tff(c_15982, plain, (![A_863, C_861, E_864]: (k2_partfun1(k4_subset_1(A_863, C_861, '#skF_4'), '#skF_2', k1_tmap_1(A_863, '#skF_2', C_861, '#skF_4', E_864, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_863, '#skF_2', C_861, '#skF_4', E_864, '#skF_6')) | k2_partfun1(C_861, '#skF_2', E_864, k9_subset_1(A_863, C_861, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_863, C_861, '#skF_4')) | ~m1_subset_1(E_864, k1_zfmisc_1(k2_zfmisc_1(C_861, '#skF_2'))) | ~v1_funct_2(E_864, C_861, '#skF_2') | ~v1_funct_1(E_864) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_863)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_861, k1_zfmisc_1(A_863)) | v1_xboole_0(C_861) | v1_xboole_0('#skF_2') | v1_xboole_0(A_863))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3854, c_15974])).
% 13.80/5.91  tff(c_20152, plain, (![A_950, C_951, E_952]: (k2_partfun1(k4_subset_1(A_950, C_951, '#skF_4'), '#skF_2', k1_tmap_1(A_950, '#skF_2', C_951, '#skF_4', E_952, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_950, '#skF_2', C_951, '#skF_4', E_952, '#skF_6')) | k2_partfun1(C_951, '#skF_2', E_952, k9_subset_1(A_950, C_951, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_950, C_951, '#skF_4')) | ~m1_subset_1(E_952, k1_zfmisc_1(k2_zfmisc_1(C_951, '#skF_2'))) | ~v1_funct_2(E_952, C_951, '#skF_2') | ~v1_funct_1(E_952) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_950)) | ~m1_subset_1(C_951, k1_zfmisc_1(A_950)) | v1_xboole_0(C_951) | v1_xboole_0(A_950))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_15982])).
% 13.80/5.91  tff(c_20157, plain, (![A_950]: (k2_partfun1(k4_subset_1(A_950, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_950, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_950, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_950, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_950, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_950)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_950)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_950))), inference(resolution, [status(thm)], [c_56, c_20152])).
% 13.80/5.91  tff(c_20165, plain, (![A_950]: (k2_partfun1(k4_subset_1(A_950, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_950, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_950, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_950, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_950, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_950)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_950)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_950))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3851, c_20157])).
% 13.80/5.91  tff(c_23690, plain, (![A_992]: (k2_partfun1(k4_subset_1(A_992, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_992, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_992, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_992, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_992, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_992)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_992)) | v1_xboole_0(A_992))), inference(negUnitSimplification, [status(thm)], [c_70, c_20165])).
% 13.80/5.91  tff(c_166, plain, (![C_230, A_231, B_232]: (v1_relat_1(C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.80/5.91  tff(c_174, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_166])).
% 13.80/5.91  tff(c_205, plain, (![C_238, A_239, B_240]: (v4_relat_1(C_238, A_239) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.80/5.91  tff(c_213, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_205])).
% 13.80/5.91  tff(c_280, plain, (![B_256, A_257]: (k1_relat_1(B_256)=A_257 | ~v1_partfun1(B_256, A_257) | ~v4_relat_1(B_256, A_257) | ~v1_relat_1(B_256))), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.80/5.91  tff(c_283, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_213, c_280])).
% 13.80/5.91  tff(c_289, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_283])).
% 13.80/5.91  tff(c_293, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_289])).
% 13.80/5.91  tff(c_937, plain, (![C_301, A_302, B_303]: (v1_partfun1(C_301, A_302) | ~v1_funct_2(C_301, A_302, B_303) | ~v1_funct_1(C_301) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_302, B_303))) | v1_xboole_0(B_303))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.80/5.91  tff(c_943, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_937])).
% 13.80/5.91  tff(c_950, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_943])).
% 13.80/5.91  tff(c_952, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_293, c_950])).
% 13.80/5.91  tff(c_953, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_289])).
% 13.80/5.91  tff(c_958, plain, (![B_15]: (k7_relat_1('#skF_6', B_15)=k1_xboole_0 | ~r1_xboole_0(B_15, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_953, c_12])).
% 13.80/5.91  tff(c_1438, plain, (![B_330]: (k7_relat_1('#skF_6', B_330)=k1_xboole_0 | ~r1_xboole_0(B_330, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_958])).
% 13.80/5.91  tff(c_1442, plain, (![A_16]: (k7_relat_1('#skF_6', A_16)=k1_xboole_0 | ~r1_subset_1(A_16, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_16, c_1438])).
% 13.80/5.91  tff(c_1457, plain, (![A_332]: (k7_relat_1('#skF_6', A_332)=k1_xboole_0 | ~r1_subset_1(A_332, '#skF_4') | v1_xboole_0(A_332))), inference(negUnitSimplification, [status(thm)], [c_66, c_1442])).
% 13.80/5.91  tff(c_1460, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1457])).
% 13.80/5.91  tff(c_1463, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_1460])).
% 13.80/5.91  tff(c_10, plain, (![C_12, A_10, B_11]: (k3_xboole_0(k7_relat_1(C_12, A_10), k7_relat_1(C_12, B_11))=k7_relat_1(C_12, k3_xboole_0(A_10, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.80/5.91  tff(c_1501, plain, (![A_10]: (k7_relat_1('#skF_6', k3_xboole_0(A_10, '#skF_3'))=k3_xboole_0(k7_relat_1('#skF_6', A_10), k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1463, c_10])).
% 13.80/5.91  tff(c_1507, plain, (![A_10]: (k7_relat_1('#skF_6', k3_xboole_0(A_10, '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_174, c_98, c_2, c_1501])).
% 13.80/5.91  tff(c_1673, plain, (![A_340, B_341, C_342, D_343]: (k2_partfun1(A_340, B_341, C_342, D_343)=k7_relat_1(C_342, D_343) | ~m1_subset_1(C_342, k1_zfmisc_1(k2_zfmisc_1(A_340, B_341))) | ~v1_funct_1(C_342))), inference(cnfTransformation, [status(thm)], [f_109])).
% 13.80/5.91  tff(c_1677, plain, (![D_343]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_343)=k7_relat_1('#skF_6', D_343) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_1673])).
% 13.80/5.91  tff(c_1683, plain, (![D_343]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_343)=k7_relat_1('#skF_6', D_343))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1677])).
% 13.80/5.91  tff(c_173, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_166])).
% 13.80/5.91  tff(c_214, plain, (![B_241, A_242]: (r1_subset_1(B_241, A_242) | ~r1_subset_1(A_242, B_241) | v1_xboole_0(B_241) | v1_xboole_0(A_242))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.80/5.91  tff(c_216, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_214])).
% 13.80/5.91  tff(c_219, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_216])).
% 13.80/5.91  tff(c_212, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_205])).
% 13.80/5.91  tff(c_286, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_212, c_280])).
% 13.80/5.91  tff(c_292, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_286])).
% 13.80/5.91  tff(c_979, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_292])).
% 13.80/5.91  tff(c_1401, plain, (![C_326, A_327, B_328]: (v1_partfun1(C_326, A_327) | ~v1_funct_2(C_326, A_327, B_328) | ~v1_funct_1(C_326) | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(A_327, B_328))) | v1_xboole_0(B_328))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.80/5.91  tff(c_1404, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_1401])).
% 13.80/5.91  tff(c_1410, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1404])).
% 13.80/5.91  tff(c_1412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_979, c_1410])).
% 13.80/5.91  tff(c_1413, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_292])).
% 13.80/5.91  tff(c_1418, plain, (![B_15]: (k7_relat_1('#skF_5', B_15)=k1_xboole_0 | ~r1_xboole_0(B_15, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1413, c_12])).
% 13.80/5.91  tff(c_1430, plain, (![B_329]: (k7_relat_1('#skF_5', B_329)=k1_xboole_0 | ~r1_xboole_0(B_329, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_1418])).
% 13.80/5.91  tff(c_1434, plain, (![A_16]: (k7_relat_1('#skF_5', A_16)=k1_xboole_0 | ~r1_subset_1(A_16, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_16, c_1430])).
% 13.80/5.91  tff(c_1446, plain, (![A_331]: (k7_relat_1('#skF_5', A_331)=k1_xboole_0 | ~r1_subset_1(A_331, '#skF_3') | v1_xboole_0(A_331))), inference(negUnitSimplification, [status(thm)], [c_70, c_1434])).
% 13.80/5.91  tff(c_1449, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_219, c_1446])).
% 13.80/5.91  tff(c_1452, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_1449])).
% 13.80/5.91  tff(c_1464, plain, (![C_333, A_334, B_335]: (k3_xboole_0(k7_relat_1(C_333, A_334), k7_relat_1(C_333, B_335))=k7_relat_1(C_333, k3_xboole_0(A_334, B_335)) | ~v1_relat_1(C_333))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.80/5.91  tff(c_1479, plain, (![B_335]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', B_335))=k3_xboole_0(k1_xboole_0, k7_relat_1('#skF_5', B_335)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1452, c_1464])).
% 13.80/5.91  tff(c_1492, plain, (![B_335]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', B_335))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_173, c_98, c_1479])).
% 13.80/5.91  tff(c_1675, plain, (![D_343]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_343)=k7_relat_1('#skF_5', D_343) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_1673])).
% 13.80/5.91  tff(c_1680, plain, (![D_343]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_343)=k7_relat_1('#skF_5', D_343))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1675])).
% 13.80/5.91  tff(c_238, plain, (![A_250, B_251, C_252]: (k9_subset_1(A_250, B_251, C_252)=k3_xboole_0(B_251, C_252) | ~m1_subset_1(C_252, k1_zfmisc_1(A_250)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.80/5.91  tff(c_250, plain, (![B_251]: (k9_subset_1('#skF_1', B_251, '#skF_4')=k3_xboole_0(B_251, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_238])).
% 13.80/5.91  tff(c_48, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_233])).
% 13.80/5.91  tff(c_165, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_48])).
% 13.80/5.91  tff(c_260, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_250, c_165])).
% 13.80/5.91  tff(c_261, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_4', '#skF_3'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_260])).
% 13.80/5.91  tff(c_1686, plain, (k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_4', '#skF_3'))!=k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1680, c_261])).
% 13.80/5.91  tff(c_1687, plain, (k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_4', '#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1492, c_1686])).
% 13.80/5.91  tff(c_1707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1507, c_1683, c_1687])).
% 13.80/5.91  tff(c_1708, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 13.80/5.91  tff(c_3041, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_1708])).
% 13.80/5.91  tff(c_23701, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_23690, c_3041])).
% 13.80/5.91  tff(c_23715, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_3769, c_3771, c_2, c_3690, c_2, c_3690, c_6489, c_23701])).
% 13.80/5.91  tff(c_23717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_23715])).
% 13.80/5.91  tff(c_23718, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_1708])).
% 13.80/5.91  tff(c_46170, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_46158, c_23718])).
% 13.80/5.91  tff(c_46184, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_24448, c_24371, c_24454, c_24371, c_26310, c_46170])).
% 13.80/5.91  tff(c_46186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_46184])).
% 13.80/5.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.80/5.91  
% 13.80/5.91  Inference rules
% 13.80/5.91  ----------------------
% 13.80/5.91  #Ref     : 0
% 13.80/5.91  #Sup     : 10532
% 13.80/5.91  #Fact    : 0
% 13.80/5.91  #Define  : 0
% 13.80/5.91  #Split   : 17
% 13.80/5.91  #Chain   : 0
% 13.80/5.91  #Close   : 0
% 13.80/5.91  
% 13.80/5.91  Ordering : KBO
% 13.80/5.91  
% 13.80/5.91  Simplification rules
% 13.80/5.91  ----------------------
% 13.80/5.91  #Subsume      : 84
% 13.80/5.91  #Demod        : 10303
% 13.80/5.91  #Tautology    : 8672
% 13.80/5.91  #SimpNegUnit  : 225
% 13.80/5.91  #BackRed      : 13
% 13.80/5.91  
% 13.80/5.91  #Partial instantiations: 0
% 13.80/5.91  #Strategies tried      : 1
% 13.80/5.91  
% 13.80/5.91  Timing (in seconds)
% 13.80/5.91  ----------------------
% 13.80/5.91  Preprocessing        : 0.44
% 13.80/5.91  Parsing              : 0.22
% 13.80/5.91  CNF conversion       : 0.06
% 13.80/5.91  Main loop            : 4.63
% 13.80/5.91  Inferencing          : 1.20
% 13.80/5.91  Reduction            : 2.35
% 13.80/5.91  Demodulation         : 2.04
% 13.80/5.91  BG Simplification    : 0.11
% 13.80/5.91  Subsumption          : 0.76
% 13.80/5.91  Abstraction          : 0.17
% 13.80/5.91  MUC search           : 0.00
% 13.80/5.91  Cooper               : 0.00
% 13.80/5.91  Total                : 5.16
% 13.80/5.91  Index Insertion      : 0.00
% 13.80/5.91  Index Deletion       : 0.00
% 13.80/5.91  Index Matching       : 0.00
% 13.80/5.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
