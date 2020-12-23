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
% DateTime   : Thu Dec  3 10:26:16 EST 2020

% Result     : Theorem 15.26s
% Output     : CNFRefutation 15.76s
% Verified   : 
% Statistics : Number of formulae       :  408 (3724 expanded)
%              Number of leaves         :   46 (1250 expanded)
%              Depth                    :   21
%              Number of atoms          : 1082 (14318 expanded)
%              Number of equality atoms :  330 (3202 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_236,negated_conjecture,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
       => r1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_194,axiom,(
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

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_160,axiom,(
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

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_93,plain,(
    ! [C_232,A_233,B_234] :
      ( v1_relat_1(C_232)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_104,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_93])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_66,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(A_16,B_17)
      | ~ r1_subset_1(A_16,B_17)
      | v1_xboole_0(B_17)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_1912,plain,(
    ! [C_429,A_430,B_431] :
      ( v4_relat_1(C_429,A_430)
      | ~ m1_subset_1(C_429,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1923,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1912])).

tff(c_25485,plain,(
    ! [B_1112,A_1113] :
      ( k1_relat_1(B_1112) = A_1113
      | ~ v1_partfun1(B_1112,A_1113)
      | ~ v4_relat_1(B_1112,A_1113)
      | ~ v1_relat_1(B_1112) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_25494,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1923,c_25485])).

tff(c_25503,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_25494])).

tff(c_25880,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_25503])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_26116,plain,(
    ! [C_1163,A_1164,B_1165] :
      ( v1_partfun1(C_1163,A_1164)
      | ~ v1_funct_2(C_1163,A_1164,B_1165)
      | ~ v1_funct_1(C_1163)
      | ~ m1_subset_1(C_1163,k1_zfmisc_1(k2_zfmisc_1(A_1164,B_1165)))
      | v1_xboole_0(B_1165) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26119,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_26116])).

tff(c_26129,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_26119])).

tff(c_26131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_25880,c_26129])).

tff(c_26132,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_25503])).

tff(c_14,plain,(
    ! [A_11,B_13] :
      ( k7_relat_1(A_11,B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,k1_relat_1(A_11))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26140,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_6',B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26132,c_14])).

tff(c_26235,plain,(
    ! [B_1170] :
      ( k7_relat_1('#skF_6',B_1170) = k1_xboole_0
      | ~ r1_xboole_0(B_1170,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_26140])).

tff(c_26239,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_6',A_16) = k1_xboole_0
      | ~ r1_subset_1(A_16,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_20,c_26235])).

tff(c_26300,plain,(
    ! [A_1178] :
      ( k7_relat_1('#skF_6',A_1178) = k1_xboole_0
      | ~ r1_subset_1(A_1178,'#skF_4')
      | v1_xboole_0(A_1178) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_26239])).

tff(c_26303,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_26300])).

tff(c_26306,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_26303])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k3_xboole_0(k1_relat_1(B_15),A_14) = k1_relat_1(k7_relat_1(B_15,A_14))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26143,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_14)) = k3_xboole_0('#skF_4',A_14)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26132,c_16])).

tff(c_26151,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1('#skF_6',A_14)) = k3_xboole_0('#skF_4',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_26143])).

tff(c_26310,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26306,c_26151])).

tff(c_25369,plain,(
    ! [B_1088,A_1089] :
      ( r1_subset_1(B_1088,A_1089)
      | ~ r1_subset_1(A_1089,B_1088)
      | v1_xboole_0(B_1088)
      | v1_xboole_0(A_1089) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_25371,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_25369])).

tff(c_25374,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_70,c_25371])).

tff(c_25380,plain,(
    ! [A_1090,B_1091] :
      ( r1_xboole_0(A_1090,B_1091)
      | ~ r1_subset_1(A_1090,B_1091)
      | v1_xboole_0(B_1091)
      | v1_xboole_0(A_1090) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26426,plain,(
    ! [A_1192,B_1193] :
      ( k3_xboole_0(A_1192,B_1193) = k1_xboole_0
      | ~ r1_subset_1(A_1192,B_1193)
      | v1_xboole_0(B_1193)
      | v1_xboole_0(A_1192) ) ),
    inference(resolution,[status(thm)],[c_25380,c_2])).

tff(c_26429,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_25374,c_26426])).

tff(c_26434,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26310,c_26429])).

tff(c_26435,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_74,c_26434])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_106,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_93])).

tff(c_26451,plain,(
    ! [B_13] :
      ( k7_relat_1(k1_xboole_0,B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26435,c_14])).

tff(c_26498,plain,(
    ! [B_1204] :
      ( k7_relat_1(k1_xboole_0,B_1204) = k1_xboole_0
      | ~ r1_xboole_0(B_1204,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_26451])).

tff(c_26506,plain,(
    ! [A_1] :
      ( k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0
      | k3_xboole_0(A_1,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_26498])).

tff(c_26510,plain,(
    ! [A_1] : k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_26506])).

tff(c_26454,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26435,c_16])).

tff(c_26462,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_26454])).

tff(c_26525,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26435,c_26510,c_26462])).

tff(c_26319,plain,(
    ! [A_1179] :
      ( k7_relat_1('#skF_6',A_1179) = k1_xboole_0
      | k3_xboole_0(A_1179,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_26235])).

tff(c_1926,plain,(
    ! [B_432,A_433] :
      ( k3_xboole_0(k1_relat_1(B_432),A_433) = k1_relat_1(k7_relat_1(B_432,A_433))
      | ~ v1_relat_1(B_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1933,plain,(
    ! [B_432] :
      ( k1_relat_1(k7_relat_1(B_432,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_432) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1926,c_6])).

tff(c_26332,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1('#skF_6')
    | k3_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26319,c_1933])).

tff(c_26342,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_26332])).

tff(c_26365,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_26342])).

tff(c_26530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26525,c_26365])).

tff(c_26531,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26342])).

tff(c_26549,plain,(
    ! [B_13] :
      ( k7_relat_1(k1_xboole_0,B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26531,c_14])).

tff(c_26631,plain,(
    ! [B_1217] :
      ( k7_relat_1(k1_xboole_0,B_1217) = k1_xboole_0
      | ~ r1_xboole_0(B_1217,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_26549])).

tff(c_26639,plain,(
    ! [A_1] :
      ( k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0
      | k3_xboole_0(A_1,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_26631])).

tff(c_26643,plain,(
    ! [A_1] : k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_26639])).

tff(c_26552,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26531,c_16])).

tff(c_26560,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_26552])).

tff(c_26658,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26531,c_26643,c_26560])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_105,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_93])).

tff(c_1924,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1912])).

tff(c_25488,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1924,c_25485])).

tff(c_25497,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_25488])).

tff(c_25504,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_25497])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_62,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_25834,plain,(
    ! [C_1143,A_1144,B_1145] :
      ( v1_partfun1(C_1143,A_1144)
      | ~ v1_funct_2(C_1143,A_1144,B_1145)
      | ~ v1_funct_1(C_1143)
      | ~ m1_subset_1(C_1143,k1_zfmisc_1(k2_zfmisc_1(A_1144,B_1145)))
      | v1_xboole_0(B_1145) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_25840,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_25834])).

tff(c_25851,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_25840])).

tff(c_25853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_25504,c_25851])).

tff(c_25854,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_25497])).

tff(c_25862,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_5',B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25854,c_14])).

tff(c_26222,plain,(
    ! [B_1169] :
      ( k7_relat_1('#skF_5',B_1169) = k1_xboole_0
      | ~ r1_xboole_0(B_1169,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_25862])).

tff(c_26282,plain,(
    ! [A_1177] :
      ( k7_relat_1('#skF_5',A_1177) = k1_xboole_0
      | k3_xboole_0(A_1177,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_26222])).

tff(c_26292,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1('#skF_5')
    | k3_xboole_0(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26282,c_1933])).

tff(c_26298,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_26292])).

tff(c_26318,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_26298])).

tff(c_26662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26658,c_26318])).

tff(c_26663,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26298])).

tff(c_26674,plain,(
    ! [B_13] :
      ( k7_relat_1(k1_xboole_0,B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26663,c_14])).

tff(c_26753,plain,(
    ! [B_1224] :
      ( k7_relat_1(k1_xboole_0,B_1224) = k1_xboole_0
      | ~ r1_xboole_0(B_1224,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_26674])).

tff(c_26761,plain,(
    ! [A_1] :
      ( k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0
      | k3_xboole_0(A_1,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_26753])).

tff(c_26765,plain,(
    ! [A_1] : k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_26761])).

tff(c_26677,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26663,c_16])).

tff(c_26685,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_26677])).

tff(c_26797,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26663,c_26765,c_26685])).

tff(c_25349,plain,(
    ! [A_1085,B_1086] :
      ( k7_relat_1(A_1085,B_1086) = k1_xboole_0
      | ~ r1_xboole_0(B_1086,k1_relat_1(A_1085))
      | ~ v1_relat_1(A_1085) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26925,plain,(
    ! [A_1249,A_1250] :
      ( k7_relat_1(A_1249,A_1250) = k1_xboole_0
      | ~ v1_relat_1(A_1249)
      | k3_xboole_0(A_1250,k1_relat_1(A_1249)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_25349])).

tff(c_26961,plain,(
    ! [A_1251] :
      ( k7_relat_1(A_1251,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_1251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26797,c_26925])).

tff(c_26974,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_26961])).

tff(c_26973,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_26961])).

tff(c_26226,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_5',A_16) = k1_xboole_0
      | ~ r1_subset_1(A_16,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_20,c_26222])).

tff(c_26716,plain,(
    ! [A_1222] :
      ( k7_relat_1('#skF_5',A_1222) = k1_xboole_0
      | ~ r1_subset_1(A_1222,'#skF_3')
      | v1_xboole_0(A_1222) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_26226])).

tff(c_26719,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_25374,c_26716])).

tff(c_26722,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_26719])).

tff(c_25865,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_14)) = k3_xboole_0('#skF_3',A_14)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25854,c_16])).

tff(c_25873,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1('#skF_5',A_14)) = k3_xboole_0('#skF_3',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_25865])).

tff(c_26729,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26722,c_25873])).

tff(c_26738,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26663,c_26729])).

tff(c_25423,plain,(
    ! [A_1102,B_1103,C_1104] :
      ( k9_subset_1(A_1102,B_1103,C_1104) = k3_xboole_0(B_1103,C_1104)
      | ~ m1_subset_1(C_1104,k1_zfmisc_1(A_1102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_25438,plain,(
    ! [B_1103] : k9_subset_1('#skF_1',B_1103,'#skF_4') = k3_xboole_0(B_1103,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_25423])).

tff(c_26780,plain,(
    ! [F_1227,C_1228,A_1230,B_1229,E_1231,D_1226] :
      ( v1_funct_1(k1_tmap_1(A_1230,B_1229,C_1228,D_1226,E_1231,F_1227))
      | ~ m1_subset_1(F_1227,k1_zfmisc_1(k2_zfmisc_1(D_1226,B_1229)))
      | ~ v1_funct_2(F_1227,D_1226,B_1229)
      | ~ v1_funct_1(F_1227)
      | ~ m1_subset_1(E_1231,k1_zfmisc_1(k2_zfmisc_1(C_1228,B_1229)))
      | ~ v1_funct_2(E_1231,C_1228,B_1229)
      | ~ v1_funct_1(E_1231)
      | ~ m1_subset_1(D_1226,k1_zfmisc_1(A_1230))
      | v1_xboole_0(D_1226)
      | ~ m1_subset_1(C_1228,k1_zfmisc_1(A_1230))
      | v1_xboole_0(C_1228)
      | v1_xboole_0(B_1229)
      | v1_xboole_0(A_1230) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_26782,plain,(
    ! [A_1230,C_1228,E_1231] :
      ( v1_funct_1(k1_tmap_1(A_1230,'#skF_2',C_1228,'#skF_4',E_1231,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1231,k1_zfmisc_1(k2_zfmisc_1(C_1228,'#skF_2')))
      | ~ v1_funct_2(E_1231,C_1228,'#skF_2')
      | ~ v1_funct_1(E_1231)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1230))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1228,k1_zfmisc_1(A_1230))
      | v1_xboole_0(C_1228)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1230) ) ),
    inference(resolution,[status(thm)],[c_54,c_26780])).

tff(c_26790,plain,(
    ! [A_1230,C_1228,E_1231] :
      ( v1_funct_1(k1_tmap_1(A_1230,'#skF_2',C_1228,'#skF_4',E_1231,'#skF_6'))
      | ~ m1_subset_1(E_1231,k1_zfmisc_1(k2_zfmisc_1(C_1228,'#skF_2')))
      | ~ v1_funct_2(E_1231,C_1228,'#skF_2')
      | ~ v1_funct_1(E_1231)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1230))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1228,k1_zfmisc_1(A_1230))
      | v1_xboole_0(C_1228)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_26782])).

tff(c_26858,plain,(
    ! [A_1235,C_1236,E_1237] :
      ( v1_funct_1(k1_tmap_1(A_1235,'#skF_2',C_1236,'#skF_4',E_1237,'#skF_6'))
      | ~ m1_subset_1(E_1237,k1_zfmisc_1(k2_zfmisc_1(C_1236,'#skF_2')))
      | ~ v1_funct_2(E_1237,C_1236,'#skF_2')
      | ~ v1_funct_1(E_1237)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1235))
      | ~ m1_subset_1(C_1236,k1_zfmisc_1(A_1235))
      | v1_xboole_0(C_1236)
      | v1_xboole_0(A_1235) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_26790])).

tff(c_26862,plain,(
    ! [A_1235] :
      ( v1_funct_1(k1_tmap_1(A_1235,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1235))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1235))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1235) ) ),
    inference(resolution,[status(thm)],[c_60,c_26858])).

tff(c_26872,plain,(
    ! [A_1235] :
      ( v1_funct_1(k1_tmap_1(A_1235,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1235))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1235))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_26862])).

tff(c_27161,plain,(
    ! [A_1271] :
      ( v1_funct_1(k1_tmap_1(A_1271,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1271))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1271))
      | v1_xboole_0(A_1271) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_26872])).

tff(c_27164,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_27161])).

tff(c_27167,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_27164])).

tff(c_27168,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_27167])).

tff(c_26248,plain,(
    ! [A_1171,B_1172,C_1173,D_1174] :
      ( k2_partfun1(A_1171,B_1172,C_1173,D_1174) = k7_relat_1(C_1173,D_1174)
      | ~ m1_subset_1(C_1173,k1_zfmisc_1(k2_zfmisc_1(A_1171,B_1172)))
      | ~ v1_funct_1(C_1173) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_26252,plain,(
    ! [D_1174] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_1174) = k7_relat_1('#skF_5',D_1174)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_26248])).

tff(c_26261,plain,(
    ! [D_1174] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1174) = k7_relat_1('#skF_5',D_1174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_26252])).

tff(c_26250,plain,(
    ! [D_1174] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_1174) = k7_relat_1('#skF_6',D_1174)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_26248])).

tff(c_26258,plain,(
    ! [D_1174] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_1174) = k7_relat_1('#skF_6',D_1174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_26250])).

tff(c_48,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_46,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_27131,plain,(
    ! [A_1266,B_1265,F_1268,E_1267,D_1264,C_1263] :
      ( k2_partfun1(k4_subset_1(A_1266,C_1263,D_1264),B_1265,k1_tmap_1(A_1266,B_1265,C_1263,D_1264,E_1267,F_1268),C_1263) = E_1267
      | ~ m1_subset_1(k1_tmap_1(A_1266,B_1265,C_1263,D_1264,E_1267,F_1268),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1266,C_1263,D_1264),B_1265)))
      | ~ v1_funct_2(k1_tmap_1(A_1266,B_1265,C_1263,D_1264,E_1267,F_1268),k4_subset_1(A_1266,C_1263,D_1264),B_1265)
      | ~ v1_funct_1(k1_tmap_1(A_1266,B_1265,C_1263,D_1264,E_1267,F_1268))
      | k2_partfun1(D_1264,B_1265,F_1268,k9_subset_1(A_1266,C_1263,D_1264)) != k2_partfun1(C_1263,B_1265,E_1267,k9_subset_1(A_1266,C_1263,D_1264))
      | ~ m1_subset_1(F_1268,k1_zfmisc_1(k2_zfmisc_1(D_1264,B_1265)))
      | ~ v1_funct_2(F_1268,D_1264,B_1265)
      | ~ v1_funct_1(F_1268)
      | ~ m1_subset_1(E_1267,k1_zfmisc_1(k2_zfmisc_1(C_1263,B_1265)))
      | ~ v1_funct_2(E_1267,C_1263,B_1265)
      | ~ v1_funct_1(E_1267)
      | ~ m1_subset_1(D_1264,k1_zfmisc_1(A_1266))
      | v1_xboole_0(D_1264)
      | ~ m1_subset_1(C_1263,k1_zfmisc_1(A_1266))
      | v1_xboole_0(C_1263)
      | v1_xboole_0(B_1265)
      | v1_xboole_0(A_1266) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_33127,plain,(
    ! [B_1470,F_1468,D_1467,C_1469,A_1471,E_1472] :
      ( k2_partfun1(k4_subset_1(A_1471,C_1469,D_1467),B_1470,k1_tmap_1(A_1471,B_1470,C_1469,D_1467,E_1472,F_1468),C_1469) = E_1472
      | ~ v1_funct_2(k1_tmap_1(A_1471,B_1470,C_1469,D_1467,E_1472,F_1468),k4_subset_1(A_1471,C_1469,D_1467),B_1470)
      | ~ v1_funct_1(k1_tmap_1(A_1471,B_1470,C_1469,D_1467,E_1472,F_1468))
      | k2_partfun1(D_1467,B_1470,F_1468,k9_subset_1(A_1471,C_1469,D_1467)) != k2_partfun1(C_1469,B_1470,E_1472,k9_subset_1(A_1471,C_1469,D_1467))
      | ~ m1_subset_1(F_1468,k1_zfmisc_1(k2_zfmisc_1(D_1467,B_1470)))
      | ~ v1_funct_2(F_1468,D_1467,B_1470)
      | ~ v1_funct_1(F_1468)
      | ~ m1_subset_1(E_1472,k1_zfmisc_1(k2_zfmisc_1(C_1469,B_1470)))
      | ~ v1_funct_2(E_1472,C_1469,B_1470)
      | ~ v1_funct_1(E_1472)
      | ~ m1_subset_1(D_1467,k1_zfmisc_1(A_1471))
      | v1_xboole_0(D_1467)
      | ~ m1_subset_1(C_1469,k1_zfmisc_1(A_1471))
      | v1_xboole_0(C_1469)
      | v1_xboole_0(B_1470)
      | v1_xboole_0(A_1471) ) ),
    inference(resolution,[status(thm)],[c_46,c_27131])).

tff(c_39175,plain,(
    ! [A_1570,D_1566,E_1571,C_1568,F_1567,B_1569] :
      ( k2_partfun1(k4_subset_1(A_1570,C_1568,D_1566),B_1569,k1_tmap_1(A_1570,B_1569,C_1568,D_1566,E_1571,F_1567),C_1568) = E_1571
      | ~ v1_funct_1(k1_tmap_1(A_1570,B_1569,C_1568,D_1566,E_1571,F_1567))
      | k2_partfun1(D_1566,B_1569,F_1567,k9_subset_1(A_1570,C_1568,D_1566)) != k2_partfun1(C_1568,B_1569,E_1571,k9_subset_1(A_1570,C_1568,D_1566))
      | ~ m1_subset_1(F_1567,k1_zfmisc_1(k2_zfmisc_1(D_1566,B_1569)))
      | ~ v1_funct_2(F_1567,D_1566,B_1569)
      | ~ v1_funct_1(F_1567)
      | ~ m1_subset_1(E_1571,k1_zfmisc_1(k2_zfmisc_1(C_1568,B_1569)))
      | ~ v1_funct_2(E_1571,C_1568,B_1569)
      | ~ v1_funct_1(E_1571)
      | ~ m1_subset_1(D_1566,k1_zfmisc_1(A_1570))
      | v1_xboole_0(D_1566)
      | ~ m1_subset_1(C_1568,k1_zfmisc_1(A_1570))
      | v1_xboole_0(C_1568)
      | v1_xboole_0(B_1569)
      | v1_xboole_0(A_1570) ) ),
    inference(resolution,[status(thm)],[c_48,c_33127])).

tff(c_39179,plain,(
    ! [A_1570,C_1568,E_1571] :
      ( k2_partfun1(k4_subset_1(A_1570,C_1568,'#skF_4'),'#skF_2',k1_tmap_1(A_1570,'#skF_2',C_1568,'#skF_4',E_1571,'#skF_6'),C_1568) = E_1571
      | ~ v1_funct_1(k1_tmap_1(A_1570,'#skF_2',C_1568,'#skF_4',E_1571,'#skF_6'))
      | k2_partfun1(C_1568,'#skF_2',E_1571,k9_subset_1(A_1570,C_1568,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1570,C_1568,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1571,k1_zfmisc_1(k2_zfmisc_1(C_1568,'#skF_2')))
      | ~ v1_funct_2(E_1571,C_1568,'#skF_2')
      | ~ v1_funct_1(E_1571)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1570))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1568,k1_zfmisc_1(A_1570))
      | v1_xboole_0(C_1568)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1570) ) ),
    inference(resolution,[status(thm)],[c_54,c_39175])).

tff(c_39188,plain,(
    ! [A_1570,C_1568,E_1571] :
      ( k2_partfun1(k4_subset_1(A_1570,C_1568,'#skF_4'),'#skF_2',k1_tmap_1(A_1570,'#skF_2',C_1568,'#skF_4',E_1571,'#skF_6'),C_1568) = E_1571
      | ~ v1_funct_1(k1_tmap_1(A_1570,'#skF_2',C_1568,'#skF_4',E_1571,'#skF_6'))
      | k2_partfun1(C_1568,'#skF_2',E_1571,k9_subset_1(A_1570,C_1568,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1570,C_1568,'#skF_4'))
      | ~ m1_subset_1(E_1571,k1_zfmisc_1(k2_zfmisc_1(C_1568,'#skF_2')))
      | ~ v1_funct_2(E_1571,C_1568,'#skF_2')
      | ~ v1_funct_1(E_1571)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1570))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1568,k1_zfmisc_1(A_1570))
      | v1_xboole_0(C_1568)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1570) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_26258,c_39179])).

tff(c_39228,plain,(
    ! [A_1580,C_1581,E_1582] :
      ( k2_partfun1(k4_subset_1(A_1580,C_1581,'#skF_4'),'#skF_2',k1_tmap_1(A_1580,'#skF_2',C_1581,'#skF_4',E_1582,'#skF_6'),C_1581) = E_1582
      | ~ v1_funct_1(k1_tmap_1(A_1580,'#skF_2',C_1581,'#skF_4',E_1582,'#skF_6'))
      | k2_partfun1(C_1581,'#skF_2',E_1582,k9_subset_1(A_1580,C_1581,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1580,C_1581,'#skF_4'))
      | ~ m1_subset_1(E_1582,k1_zfmisc_1(k2_zfmisc_1(C_1581,'#skF_2')))
      | ~ v1_funct_2(E_1582,C_1581,'#skF_2')
      | ~ v1_funct_1(E_1582)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1580))
      | ~ m1_subset_1(C_1581,k1_zfmisc_1(A_1580))
      | v1_xboole_0(C_1581)
      | v1_xboole_0(A_1580) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_39188])).

tff(c_39235,plain,(
    ! [A_1580] :
      ( k2_partfun1(k4_subset_1(A_1580,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1580,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1580,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1580,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1580,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1580))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1580))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1580) ) ),
    inference(resolution,[status(thm)],[c_60,c_39228])).

tff(c_39248,plain,(
    ! [A_1580] :
      ( k2_partfun1(k4_subset_1(A_1580,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1580,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1580,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1580,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1580,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1580))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1580))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1580) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_26261,c_39235])).

tff(c_47616,plain,(
    ! [A_1695] :
      ( k2_partfun1(k4_subset_1(A_1695,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1695,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1695,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1695,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1695,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1695))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1695))
      | v1_xboole_0(A_1695) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_39248])).

tff(c_2028,plain,(
    ! [B_454,A_455] :
      ( k1_relat_1(B_454) = A_455
      | ~ v1_partfun1(B_454,A_455)
      | ~ v4_relat_1(B_454,A_455)
      | ~ v1_relat_1(B_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2037,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1923,c_2028])).

tff(c_2046,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_2037])).

tff(c_2531,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2046])).

tff(c_2762,plain,(
    ! [C_529,A_530,B_531] :
      ( v1_partfun1(C_529,A_530)
      | ~ v1_funct_2(C_529,A_530,B_531)
      | ~ v1_funct_1(C_529)
      | ~ m1_subset_1(C_529,k1_zfmisc_1(k2_zfmisc_1(A_530,B_531)))
      | v1_xboole_0(B_531) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2765,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_2762])).

tff(c_2775,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2765])).

tff(c_2777,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2531,c_2775])).

tff(c_2778,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2046])).

tff(c_2786,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_6',B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2778,c_14])).

tff(c_2837,plain,(
    ! [B_534] :
      ( k7_relat_1('#skF_6',B_534) = k1_xboole_0
      | ~ r1_xboole_0(B_534,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_2786])).

tff(c_2841,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_6',A_16) = k1_xboole_0
      | ~ r1_subset_1(A_16,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_20,c_2837])).

tff(c_3026,plain,(
    ! [A_554] :
      ( k7_relat_1('#skF_6',A_554) = k1_xboole_0
      | ~ r1_subset_1(A_554,'#skF_4')
      | v1_xboole_0(A_554) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2841])).

tff(c_3029,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_3026])).

tff(c_3032,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3029])).

tff(c_2789,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_14)) = k3_xboole_0('#skF_4',A_14)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2778,c_16])).

tff(c_2797,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1('#skF_6',A_14)) = k3_xboole_0('#skF_4',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_2789])).

tff(c_3039,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3032,c_2797])).

tff(c_1977,plain,(
    ! [B_439,A_440] :
      ( r1_subset_1(B_439,A_440)
      | ~ r1_subset_1(A_440,B_439)
      | v1_xboole_0(B_439)
      | v1_xboole_0(A_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1979,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1977])).

tff(c_1982,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_70,c_1979])).

tff(c_1988,plain,(
    ! [A_441,B_442] :
      ( r1_xboole_0(A_441,B_442)
      | ~ r1_subset_1(A_441,B_442)
      | v1_xboole_0(B_442)
      | v1_xboole_0(A_441) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3157,plain,(
    ! [A_567,B_568] :
      ( k3_xboole_0(A_567,B_568) = k1_xboole_0
      | ~ r1_subset_1(A_567,B_568)
      | v1_xboole_0(B_568)
      | v1_xboole_0(A_567) ) ),
    inference(resolution,[status(thm)],[c_1988,c_2])).

tff(c_3160,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1982,c_3157])).

tff(c_3165,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3039,c_3160])).

tff(c_3166,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_74,c_3165])).

tff(c_3186,plain,(
    ! [B_13] :
      ( k7_relat_1(k1_xboole_0,B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3166,c_14])).

tff(c_3267,plain,(
    ! [B_577] :
      ( k7_relat_1(k1_xboole_0,B_577) = k1_xboole_0
      | ~ r1_xboole_0(B_577,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3186])).

tff(c_3275,plain,(
    ! [A_1] :
      ( k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0
      | k3_xboole_0(A_1,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_3267])).

tff(c_3279,plain,(
    ! [A_1] : k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3275])).

tff(c_3189,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3166,c_16])).

tff(c_3197,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3189])).

tff(c_3298,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3279,c_3197])).

tff(c_3299,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3166,c_3298])).

tff(c_2031,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1924,c_2028])).

tff(c_2040,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_2031])).

tff(c_2047,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2040])).

tff(c_2489,plain,(
    ! [C_503,A_504,B_505] :
      ( v1_partfun1(C_503,A_504)
      | ~ v1_funct_2(C_503,A_504,B_505)
      | ~ v1_funct_1(C_503)
      | ~ m1_subset_1(C_503,k1_zfmisc_1(k2_zfmisc_1(A_504,B_505)))
      | v1_xboole_0(B_505) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2495,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_2489])).

tff(c_2506,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2495])).

tff(c_2508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2047,c_2506])).

tff(c_2509,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2040])).

tff(c_2517,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_5',B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2509,c_14])).

tff(c_2850,plain,(
    ! [B_535] :
      ( k7_relat_1('#skF_5',B_535) = k1_xboole_0
      | ~ r1_xboole_0(B_535,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_2517])).

tff(c_2965,plain,(
    ! [A_546] :
      ( k7_relat_1('#skF_5',A_546) = k1_xboole_0
      | k3_xboole_0(A_546,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2850])).

tff(c_2975,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1('#skF_5')
    | k3_xboole_0(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2965,c_1933])).

tff(c_2981,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_2975])).

tff(c_2983,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2981])).

tff(c_3317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3299,c_2983])).

tff(c_3318,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2981])).

tff(c_3328,plain,(
    ! [B_13] :
      ( k7_relat_1(k1_xboole_0,B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3318,c_14])).

tff(c_3407,plain,(
    ! [B_589] :
      ( k7_relat_1(k1_xboole_0,B_589) = k1_xboole_0
      | ~ r1_xboole_0(B_589,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3328])).

tff(c_3415,plain,(
    ! [A_1] :
      ( k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0
      | k3_xboole_0(A_1,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_3407])).

tff(c_3419,plain,(
    ! [A_1] : k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3415])).

tff(c_3331,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3318,c_16])).

tff(c_3339,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3331])).

tff(c_3421,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3419,c_3339])).

tff(c_3422,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3318,c_3421])).

tff(c_2894,plain,(
    ! [A_537] :
      ( k7_relat_1('#skF_6',A_537) = k1_xboole_0
      | k3_xboole_0(A_537,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2837])).

tff(c_2904,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1('#skF_6')
    | k3_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2894,c_1933])).

tff(c_2910,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_2904])).

tff(c_2964,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2910])).

tff(c_3439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3422,c_2964])).

tff(c_3440,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2910])).

tff(c_3450,plain,(
    ! [B_13] :
      ( k7_relat_1(k1_xboole_0,B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3440,c_14])).

tff(c_3529,plain,(
    ! [B_598] :
      ( k7_relat_1(k1_xboole_0,B_598) = k1_xboole_0
      | ~ r1_xboole_0(B_598,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3450])).

tff(c_3537,plain,(
    ! [A_1] :
      ( k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0
      | k3_xboole_0(A_1,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_3529])).

tff(c_3541,plain,(
    ! [A_1] : k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3537])).

tff(c_3453,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3440,c_16])).

tff(c_3461,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3453])).

tff(c_3543,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3541,c_3461])).

tff(c_3544,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3440,c_3543])).

tff(c_1957,plain,(
    ! [A_436,B_437] :
      ( k7_relat_1(A_436,B_437) = k1_xboole_0
      | ~ r1_xboole_0(B_437,k1_relat_1(A_436))
      | ~ v1_relat_1(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3785,plain,(
    ! [A_624,A_625] :
      ( k7_relat_1(A_624,A_625) = k1_xboole_0
      | ~ v1_relat_1(A_624)
      | k3_xboole_0(A_625,k1_relat_1(A_624)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1957])).

tff(c_3821,plain,(
    ! [A_626] :
      ( k7_relat_1(A_626,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_626) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3544,c_3785])).

tff(c_3834,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_3821])).

tff(c_3833,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_3821])).

tff(c_2854,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_5',A_16) = k1_xboole_0
      | ~ r1_subset_1(A_16,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_20,c_2850])).

tff(c_3640,plain,(
    ! [A_608] :
      ( k7_relat_1('#skF_5',A_608) = k1_xboole_0
      | ~ r1_subset_1(A_608,'#skF_3')
      | v1_xboole_0(A_608) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2854])).

tff(c_3643,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1982,c_3640])).

tff(c_3646,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3643])).

tff(c_2520,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_14)) = k3_xboole_0('#skF_3',A_14)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2509,c_16])).

tff(c_2528,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1('#skF_5',A_14)) = k3_xboole_0('#skF_3',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_2520])).

tff(c_3653,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3646,c_2528])).

tff(c_3660,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3440,c_3653])).

tff(c_2912,plain,(
    ! [A_538,B_539,C_540] :
      ( k9_subset_1(A_538,B_539,C_540) = k3_xboole_0(B_539,C_540)
      | ~ m1_subset_1(C_540,k1_zfmisc_1(A_538)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2927,plain,(
    ! [B_539] : k9_subset_1('#skF_1',B_539,'#skF_4') = k3_xboole_0(B_539,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_2912])).

tff(c_3702,plain,(
    ! [C_612,E_615,A_614,B_613,F_611,D_610] :
      ( v1_funct_1(k1_tmap_1(A_614,B_613,C_612,D_610,E_615,F_611))
      | ~ m1_subset_1(F_611,k1_zfmisc_1(k2_zfmisc_1(D_610,B_613)))
      | ~ v1_funct_2(F_611,D_610,B_613)
      | ~ v1_funct_1(F_611)
      | ~ m1_subset_1(E_615,k1_zfmisc_1(k2_zfmisc_1(C_612,B_613)))
      | ~ v1_funct_2(E_615,C_612,B_613)
      | ~ v1_funct_1(E_615)
      | ~ m1_subset_1(D_610,k1_zfmisc_1(A_614))
      | v1_xboole_0(D_610)
      | ~ m1_subset_1(C_612,k1_zfmisc_1(A_614))
      | v1_xboole_0(C_612)
      | v1_xboole_0(B_613)
      | v1_xboole_0(A_614) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_3704,plain,(
    ! [A_614,C_612,E_615] :
      ( v1_funct_1(k1_tmap_1(A_614,'#skF_2',C_612,'#skF_4',E_615,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_615,k1_zfmisc_1(k2_zfmisc_1(C_612,'#skF_2')))
      | ~ v1_funct_2(E_615,C_612,'#skF_2')
      | ~ v1_funct_1(E_615)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_614))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_612,k1_zfmisc_1(A_614))
      | v1_xboole_0(C_612)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_614) ) ),
    inference(resolution,[status(thm)],[c_54,c_3702])).

tff(c_3712,plain,(
    ! [A_614,C_612,E_615] :
      ( v1_funct_1(k1_tmap_1(A_614,'#skF_2',C_612,'#skF_4',E_615,'#skF_6'))
      | ~ m1_subset_1(E_615,k1_zfmisc_1(k2_zfmisc_1(C_612,'#skF_2')))
      | ~ v1_funct_2(E_615,C_612,'#skF_2')
      | ~ v1_funct_1(E_615)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_614))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_612,k1_zfmisc_1(A_614))
      | v1_xboole_0(C_612)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_614) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_3704])).

tff(c_5219,plain,(
    ! [A_699,C_700,E_701] :
      ( v1_funct_1(k1_tmap_1(A_699,'#skF_2',C_700,'#skF_4',E_701,'#skF_6'))
      | ~ m1_subset_1(E_701,k1_zfmisc_1(k2_zfmisc_1(C_700,'#skF_2')))
      | ~ v1_funct_2(E_701,C_700,'#skF_2')
      | ~ v1_funct_1(E_701)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_699))
      | ~ m1_subset_1(C_700,k1_zfmisc_1(A_699))
      | v1_xboole_0(C_700)
      | v1_xboole_0(A_699) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_3712])).

tff(c_5226,plain,(
    ! [A_699] :
      ( v1_funct_1(k1_tmap_1(A_699,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_699))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_699))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_699) ) ),
    inference(resolution,[status(thm)],[c_60,c_5219])).

tff(c_5239,plain,(
    ! [A_699] :
      ( v1_funct_1(k1_tmap_1(A_699,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_699))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_699))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_699) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_5226])).

tff(c_5898,plain,(
    ! [A_716] :
      ( v1_funct_1(k1_tmap_1(A_716,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_716))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_716))
      | v1_xboole_0(A_716) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_5239])).

tff(c_5901,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_5898])).

tff(c_5904,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5901])).

tff(c_5905,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5904])).

tff(c_3463,plain,(
    ! [A_591,B_592,C_593,D_594] :
      ( k2_partfun1(A_591,B_592,C_593,D_594) = k7_relat_1(C_593,D_594)
      | ~ m1_subset_1(C_593,k1_zfmisc_1(k2_zfmisc_1(A_591,B_592)))
      | ~ v1_funct_1(C_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3467,plain,(
    ! [D_594] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_594) = k7_relat_1('#skF_5',D_594)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_3463])).

tff(c_3476,plain,(
    ! [D_594] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_594) = k7_relat_1('#skF_5',D_594) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3467])).

tff(c_3465,plain,(
    ! [D_594] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_594) = k7_relat_1('#skF_6',D_594)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_3463])).

tff(c_3473,plain,(
    ! [D_594] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_594) = k7_relat_1('#skF_6',D_594) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3465])).

tff(c_4355,plain,(
    ! [A_667,F_669,B_666,D_665,E_668,C_664] :
      ( k2_partfun1(k4_subset_1(A_667,C_664,D_665),B_666,k1_tmap_1(A_667,B_666,C_664,D_665,E_668,F_669),D_665) = F_669
      | ~ m1_subset_1(k1_tmap_1(A_667,B_666,C_664,D_665,E_668,F_669),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_667,C_664,D_665),B_666)))
      | ~ v1_funct_2(k1_tmap_1(A_667,B_666,C_664,D_665,E_668,F_669),k4_subset_1(A_667,C_664,D_665),B_666)
      | ~ v1_funct_1(k1_tmap_1(A_667,B_666,C_664,D_665,E_668,F_669))
      | k2_partfun1(D_665,B_666,F_669,k9_subset_1(A_667,C_664,D_665)) != k2_partfun1(C_664,B_666,E_668,k9_subset_1(A_667,C_664,D_665))
      | ~ m1_subset_1(F_669,k1_zfmisc_1(k2_zfmisc_1(D_665,B_666)))
      | ~ v1_funct_2(F_669,D_665,B_666)
      | ~ v1_funct_1(F_669)
      | ~ m1_subset_1(E_668,k1_zfmisc_1(k2_zfmisc_1(C_664,B_666)))
      | ~ v1_funct_2(E_668,C_664,B_666)
      | ~ v1_funct_1(E_668)
      | ~ m1_subset_1(D_665,k1_zfmisc_1(A_667))
      | v1_xboole_0(D_665)
      | ~ m1_subset_1(C_664,k1_zfmisc_1(A_667))
      | v1_xboole_0(C_664)
      | v1_xboole_0(B_666)
      | v1_xboole_0(A_667) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_10116,plain,(
    ! [B_847,E_849,C_846,A_848,D_844,F_845] :
      ( k2_partfun1(k4_subset_1(A_848,C_846,D_844),B_847,k1_tmap_1(A_848,B_847,C_846,D_844,E_849,F_845),D_844) = F_845
      | ~ v1_funct_2(k1_tmap_1(A_848,B_847,C_846,D_844,E_849,F_845),k4_subset_1(A_848,C_846,D_844),B_847)
      | ~ v1_funct_1(k1_tmap_1(A_848,B_847,C_846,D_844,E_849,F_845))
      | k2_partfun1(D_844,B_847,F_845,k9_subset_1(A_848,C_846,D_844)) != k2_partfun1(C_846,B_847,E_849,k9_subset_1(A_848,C_846,D_844))
      | ~ m1_subset_1(F_845,k1_zfmisc_1(k2_zfmisc_1(D_844,B_847)))
      | ~ v1_funct_2(F_845,D_844,B_847)
      | ~ v1_funct_1(F_845)
      | ~ m1_subset_1(E_849,k1_zfmisc_1(k2_zfmisc_1(C_846,B_847)))
      | ~ v1_funct_2(E_849,C_846,B_847)
      | ~ v1_funct_1(E_849)
      | ~ m1_subset_1(D_844,k1_zfmisc_1(A_848))
      | v1_xboole_0(D_844)
      | ~ m1_subset_1(C_846,k1_zfmisc_1(A_848))
      | v1_xboole_0(C_846)
      | v1_xboole_0(B_847)
      | v1_xboole_0(A_848) ) ),
    inference(resolution,[status(thm)],[c_46,c_4355])).

tff(c_16225,plain,(
    ! [E_953,C_950,D_948,A_952,B_951,F_949] :
      ( k2_partfun1(k4_subset_1(A_952,C_950,D_948),B_951,k1_tmap_1(A_952,B_951,C_950,D_948,E_953,F_949),D_948) = F_949
      | ~ v1_funct_1(k1_tmap_1(A_952,B_951,C_950,D_948,E_953,F_949))
      | k2_partfun1(D_948,B_951,F_949,k9_subset_1(A_952,C_950,D_948)) != k2_partfun1(C_950,B_951,E_953,k9_subset_1(A_952,C_950,D_948))
      | ~ m1_subset_1(F_949,k1_zfmisc_1(k2_zfmisc_1(D_948,B_951)))
      | ~ v1_funct_2(F_949,D_948,B_951)
      | ~ v1_funct_1(F_949)
      | ~ m1_subset_1(E_953,k1_zfmisc_1(k2_zfmisc_1(C_950,B_951)))
      | ~ v1_funct_2(E_953,C_950,B_951)
      | ~ v1_funct_1(E_953)
      | ~ m1_subset_1(D_948,k1_zfmisc_1(A_952))
      | v1_xboole_0(D_948)
      | ~ m1_subset_1(C_950,k1_zfmisc_1(A_952))
      | v1_xboole_0(C_950)
      | v1_xboole_0(B_951)
      | v1_xboole_0(A_952) ) ),
    inference(resolution,[status(thm)],[c_48,c_10116])).

tff(c_16229,plain,(
    ! [A_952,C_950,E_953] :
      ( k2_partfun1(k4_subset_1(A_952,C_950,'#skF_4'),'#skF_2',k1_tmap_1(A_952,'#skF_2',C_950,'#skF_4',E_953,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_952,'#skF_2',C_950,'#skF_4',E_953,'#skF_6'))
      | k2_partfun1(C_950,'#skF_2',E_953,k9_subset_1(A_952,C_950,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_952,C_950,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_953,k1_zfmisc_1(k2_zfmisc_1(C_950,'#skF_2')))
      | ~ v1_funct_2(E_953,C_950,'#skF_2')
      | ~ v1_funct_1(E_953)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_952))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_950,k1_zfmisc_1(A_952))
      | v1_xboole_0(C_950)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_952) ) ),
    inference(resolution,[status(thm)],[c_54,c_16225])).

tff(c_16238,plain,(
    ! [A_952,C_950,E_953] :
      ( k2_partfun1(k4_subset_1(A_952,C_950,'#skF_4'),'#skF_2',k1_tmap_1(A_952,'#skF_2',C_950,'#skF_4',E_953,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_952,'#skF_2',C_950,'#skF_4',E_953,'#skF_6'))
      | k2_partfun1(C_950,'#skF_2',E_953,k9_subset_1(A_952,C_950,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_952,C_950,'#skF_4'))
      | ~ m1_subset_1(E_953,k1_zfmisc_1(k2_zfmisc_1(C_950,'#skF_2')))
      | ~ v1_funct_2(E_953,C_950,'#skF_2')
      | ~ v1_funct_1(E_953)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_952))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_950,k1_zfmisc_1(A_952))
      | v1_xboole_0(C_950)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_952) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_3473,c_16229])).

tff(c_21181,plain,(
    ! [A_1045,C_1046,E_1047] :
      ( k2_partfun1(k4_subset_1(A_1045,C_1046,'#skF_4'),'#skF_2',k1_tmap_1(A_1045,'#skF_2',C_1046,'#skF_4',E_1047,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1045,'#skF_2',C_1046,'#skF_4',E_1047,'#skF_6'))
      | k2_partfun1(C_1046,'#skF_2',E_1047,k9_subset_1(A_1045,C_1046,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1045,C_1046,'#skF_4'))
      | ~ m1_subset_1(E_1047,k1_zfmisc_1(k2_zfmisc_1(C_1046,'#skF_2')))
      | ~ v1_funct_2(E_1047,C_1046,'#skF_2')
      | ~ v1_funct_1(E_1047)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1045))
      | ~ m1_subset_1(C_1046,k1_zfmisc_1(A_1045))
      | v1_xboole_0(C_1046)
      | v1_xboole_0(A_1045) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_16238])).

tff(c_21188,plain,(
    ! [A_1045] :
      ( k2_partfun1(k4_subset_1(A_1045,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1045,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1045,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1045,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1045,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1045))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1045))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1045) ) ),
    inference(resolution,[status(thm)],[c_60,c_21181])).

tff(c_21201,plain,(
    ! [A_1045] :
      ( k2_partfun1(k4_subset_1(A_1045,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1045,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1045,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1045,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1045,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1045))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1045))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1045) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_3476,c_21188])).

tff(c_25307,plain,(
    ! [A_1083] :
      ( k2_partfun1(k4_subset_1(A_1083,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1083,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1083,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1083,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1083,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1083))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1083))
      | v1_xboole_0(A_1083) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_21201])).

tff(c_122,plain,(
    ! [C_238,A_239,B_240] :
      ( v4_relat_1(C_238,A_239)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_133,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_122])).

tff(c_299,plain,(
    ! [B_273,A_274] :
      ( k1_relat_1(B_273) = A_274
      | ~ v1_partfun1(B_273,A_274)
      | ~ v4_relat_1(B_273,A_274)
      | ~ v1_relat_1(B_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_308,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_133,c_299])).

tff(c_317,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_308])).

tff(c_543,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_597,plain,(
    ! [C_299,A_300,B_301] :
      ( v1_partfun1(C_299,A_300)
      | ~ v1_funct_2(C_299,A_300,B_301)
      | ~ v1_funct_1(C_299)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_300,B_301)))
      | v1_xboole_0(B_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_600,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_597])).

tff(c_610,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_600])).

tff(c_612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_543,c_610])).

tff(c_613,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_624,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_6',B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_14])).

tff(c_644,plain,(
    ! [B_303] :
      ( k7_relat_1('#skF_6',B_303) = k1_xboole_0
      | ~ r1_xboole_0(B_303,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_624])).

tff(c_648,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_6',A_16) = k1_xboole_0
      | ~ r1_subset_1(A_16,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_20,c_644])).

tff(c_816,plain,(
    ! [A_313] :
      ( k7_relat_1('#skF_6',A_313) = k1_xboole_0
      | ~ r1_subset_1(A_313,'#skF_4')
      | v1_xboole_0(A_313) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_648])).

tff(c_819,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_816])).

tff(c_822,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_819])).

tff(c_621,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_14)) = k3_xboole_0('#skF_4',A_14)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_16])).

tff(c_630,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1('#skF_6',A_14)) = k3_xboole_0('#skF_4',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_621])).

tff(c_846,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_822,c_630])).

tff(c_202,plain,(
    ! [B_259,A_260] :
      ( r1_subset_1(B_259,A_260)
      | ~ r1_subset_1(A_260,B_259)
      | v1_xboole_0(B_259)
      | v1_xboole_0(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_204,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_202])).

tff(c_207,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_70,c_204])).

tff(c_213,plain,(
    ! [A_261,B_262] :
      ( r1_xboole_0(A_261,B_262)
      | ~ r1_subset_1(A_261,B_262)
      | v1_xboole_0(B_262)
      | v1_xboole_0(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_893,plain,(
    ! [A_325,B_326] :
      ( k3_xboole_0(A_325,B_326) = k1_xboole_0
      | ~ r1_subset_1(A_325,B_326)
      | v1_xboole_0(B_326)
      | v1_xboole_0(A_325) ) ),
    inference(resolution,[status(thm)],[c_213,c_2])).

tff(c_896,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_207,c_893])).

tff(c_901,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_846,c_896])).

tff(c_902,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_74,c_901])).

tff(c_921,plain,(
    ! [B_13] :
      ( k7_relat_1(k1_xboole_0,B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_902,c_14])).

tff(c_986,plain,(
    ! [B_336] :
      ( k7_relat_1(k1_xboole_0,B_336) = k1_xboole_0
      | ~ r1_xboole_0(B_336,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_921])).

tff(c_994,plain,(
    ! [A_1] :
      ( k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0
      | k3_xboole_0(A_1,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_986])).

tff(c_998,plain,(
    ! [A_1] : k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_994])).

tff(c_918,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_902,c_16])).

tff(c_927,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_918])).

tff(c_1035,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_998,c_927])).

tff(c_1036,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_902,c_1035])).

tff(c_134,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_122])).

tff(c_305,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_134,c_299])).

tff(c_314,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_305])).

tff(c_339,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_314])).

tff(c_492,plain,(
    ! [C_292,A_293,B_294] :
      ( v1_partfun1(C_292,A_293)
      | ~ v1_funct_2(C_292,A_293,B_294)
      | ~ v1_funct_1(C_292)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294)))
      | v1_xboole_0(B_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_498,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_492])).

tff(c_509,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_498])).

tff(c_511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_339,c_509])).

tff(c_512,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_523,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_5',B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_14])).

tff(c_688,plain,(
    ! [B_305] :
      ( k7_relat_1('#skF_5',B_305) = k1_xboole_0
      | ~ r1_xboole_0(B_305,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_523])).

tff(c_771,plain,(
    ! [A_311] :
      ( k7_relat_1('#skF_5',A_311) = k1_xboole_0
      | k3_xboole_0(A_311,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_688])).

tff(c_162,plain,(
    ! [B_251,A_252] :
      ( k3_xboole_0(k1_relat_1(B_251),A_252) = k1_relat_1(k7_relat_1(B_251,A_252))
      | ~ v1_relat_1(B_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_169,plain,(
    ! [B_251] :
      ( k1_relat_1(k7_relat_1(B_251,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_6])).

tff(c_781,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1('#skF_5')
    | k3_xboole_0(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_169])).

tff(c_787,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_781])).

tff(c_815,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_787])).

tff(c_1054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1036,c_815])).

tff(c_1055,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_787])).

tff(c_1069,plain,(
    ! [B_13] :
      ( k7_relat_1(k1_xboole_0,B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_14])).

tff(c_1186,plain,(
    ! [B_356] :
      ( k7_relat_1(k1_xboole_0,B_356) = k1_xboole_0
      | ~ r1_xboole_0(B_356,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1069])).

tff(c_1194,plain,(
    ! [A_1] :
      ( k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0
      | k3_xboole_0(A_1,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1186])).

tff(c_1198,plain,(
    ! [A_1] : k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1194])).

tff(c_1066,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_16])).

tff(c_1075,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1066])).

tff(c_1200,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_1075])).

tff(c_1201,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_1200])).

tff(c_732,plain,(
    ! [A_307] :
      ( k7_relat_1('#skF_6',A_307) = k1_xboole_0
      | k3_xboole_0(A_307,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_644])).

tff(c_742,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1('#skF_6')
    | k3_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_732,c_169])).

tff(c_748,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_742])).

tff(c_770,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_748])).

tff(c_1218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1201,c_770])).

tff(c_1219,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_748])).

tff(c_1232,plain,(
    ! [B_13] :
      ( k7_relat_1(k1_xboole_0,B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1219,c_14])).

tff(c_1297,plain,(
    ! [B_366] :
      ( k7_relat_1(k1_xboole_0,B_366) = k1_xboole_0
      | ~ r1_xboole_0(B_366,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1232])).

tff(c_1305,plain,(
    ! [A_1] :
      ( k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0
      | k3_xboole_0(A_1,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1297])).

tff(c_1309,plain,(
    ! [A_1] : k7_relat_1(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1305])).

tff(c_1229,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1219,c_16])).

tff(c_1238,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1(k1_xboole_0,A_14)) = k3_xboole_0(k1_xboole_0,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1229])).

tff(c_1324,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1309,c_1238])).

tff(c_138,plain,(
    ! [A_243,B_244] :
      ( k7_relat_1(A_243,B_244) = k1_xboole_0
      | ~ r1_xboole_0(B_244,k1_relat_1(A_243))
      | ~ v1_relat_1(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1462,plain,(
    ! [A_387,A_388] :
      ( k7_relat_1(A_387,A_388) = k1_xboole_0
      | ~ v1_relat_1(A_387)
      | k3_xboole_0(A_388,k1_relat_1(A_387)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_138])).

tff(c_1498,plain,(
    ! [A_389] :
      ( k7_relat_1(A_389,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_389) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1324,c_1462])).

tff(c_1511,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_1498])).

tff(c_1510,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_1498])).

tff(c_1270,plain,(
    ! [A_365] :
      ( k7_relat_1('#skF_6',A_365) = k1_xboole_0
      | ~ r1_subset_1(A_365,'#skF_4')
      | v1_xboole_0(A_365) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_648])).

tff(c_1273,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1270])).

tff(c_1276,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1273])).

tff(c_1283,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1276,c_630])).

tff(c_1290,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1283])).

tff(c_1342,plain,(
    ! [A_375] :
      ( k7_relat_1('#skF_5',A_375) = k1_xboole_0
      | k3_xboole_0(A_375,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_688])).

tff(c_520,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_14)) = k3_xboole_0('#skF_3',A_14)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_16])).

tff(c_529,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1('#skF_5',A_14)) = k3_xboole_0('#skF_3',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_520])).

tff(c_1348,plain,(
    ! [A_375] :
      ( k3_xboole_0('#skF_3',A_375) = k1_relat_1(k1_xboole_0)
      | k3_xboole_0(A_375,'#skF_3') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1342,c_529])).

tff(c_1361,plain,(
    ! [A_376] :
      ( k3_xboole_0('#skF_3',A_376) = k1_xboole_0
      | k3_xboole_0(A_376,'#skF_3') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1348])).

tff(c_1372,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1290,c_1361])).

tff(c_324,plain,(
    ! [A_276,B_277,C_278,D_279] :
      ( k2_partfun1(A_276,B_277,C_278,D_279) = k7_relat_1(C_278,D_279)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277)))
      | ~ v1_funct_1(C_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_328,plain,(
    ! [D_279] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_279) = k7_relat_1('#skF_5',D_279)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_324])).

tff(c_337,plain,(
    ! [D_279] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_279) = k7_relat_1('#skF_5',D_279) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_328])).

tff(c_326,plain,(
    ! [D_279] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_279) = k7_relat_1('#skF_6',D_279)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_324])).

tff(c_334,plain,(
    ! [D_279] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_279) = k7_relat_1('#skF_6',D_279) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_326])).

tff(c_238,plain,(
    ! [A_264,B_265,C_266] :
      ( k9_subset_1(A_264,B_265,C_266) = k3_xboole_0(B_265,C_266)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(A_264)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_253,plain,(
    ! [B_265] : k9_subset_1('#skF_1',B_265,'#skF_4') = k3_xboole_0(B_265,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_238])).

tff(c_52,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_107,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_262,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_253,c_107])).

tff(c_1890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1511,c_1510,c_1372,c_1372,c_337,c_334,c_262])).

tff(c_1891,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1944,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1891])).

tff(c_25318,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_25307,c_1944])).

tff(c_25332,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_3834,c_3833,c_3660,c_3660,c_2927,c_2927,c_5905,c_25318])).

tff(c_25334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_25332])).

tff(c_25335,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1891])).

tff(c_47625,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_47616,c_25335])).

tff(c_47636,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_26974,c_26973,c_26738,c_26738,c_25438,c_25438,c_27168,c_47625])).

tff(c_47638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_47636])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.26/7.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.51/7.86  
% 15.51/7.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.51/7.86  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 15.51/7.86  
% 15.51/7.86  %Foreground sorts:
% 15.51/7.86  
% 15.51/7.86  
% 15.51/7.86  %Background operators:
% 15.51/7.86  
% 15.51/7.86  
% 15.51/7.86  %Foreground operators:
% 15.51/7.86  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 15.51/7.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.51/7.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.51/7.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.51/7.86  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 15.51/7.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.51/7.86  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 15.51/7.86  tff('#skF_5', type, '#skF_5': $i).
% 15.51/7.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.51/7.86  tff('#skF_6', type, '#skF_6': $i).
% 15.51/7.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.51/7.86  tff('#skF_2', type, '#skF_2': $i).
% 15.51/7.86  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 15.51/7.86  tff('#skF_3', type, '#skF_3': $i).
% 15.51/7.86  tff('#skF_1', type, '#skF_1': $i).
% 15.51/7.86  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 15.51/7.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.51/7.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.51/7.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.51/7.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.51/7.86  tff('#skF_4', type, '#skF_4': $i).
% 15.51/7.86  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.51/7.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.51/7.86  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 15.51/7.86  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 15.51/7.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.51/7.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.51/7.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.51/7.86  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 15.51/7.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.51/7.86  
% 15.76/7.91  tff(f_236, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 15.76/7.91  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 15.76/7.91  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 15.76/7.91  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 15.76/7.91  tff(f_106, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 15.76/7.91  tff(f_98, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 15.76/7.91  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 15.76/7.91  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 15.76/7.91  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) => r1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_subset_1)).
% 15.76/7.91  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 15.76/7.91  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 15.76/7.91  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 15.76/7.91  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 15.76/7.91  tff(f_194, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 15.76/7.91  tff(f_112, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 15.76/7.91  tff(f_160, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 15.76/7.91  tff(c_78, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_236])).
% 15.76/7.91  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_236])).
% 15.76/7.91  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_236])).
% 15.76/7.91  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_236])).
% 15.76/7.91  tff(c_93, plain, (![C_232, A_233, B_234]: (v1_relat_1(C_232) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 15.76/7.91  tff(c_104, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_93])).
% 15.76/7.91  tff(c_70, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_236])).
% 15.76/7.91  tff(c_74, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_236])).
% 15.76/7.91  tff(c_66, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_236])).
% 15.76/7.91  tff(c_20, plain, (![A_16, B_17]: (r1_xboole_0(A_16, B_17) | ~r1_subset_1(A_16, B_17) | v1_xboole_0(B_17) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.76/7.91  tff(c_76, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_236])).
% 15.76/7.91  tff(c_1912, plain, (![C_429, A_430, B_431]: (v4_relat_1(C_429, A_430) | ~m1_subset_1(C_429, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.76/7.91  tff(c_1923, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_1912])).
% 15.76/7.91  tff(c_25485, plain, (![B_1112, A_1113]: (k1_relat_1(B_1112)=A_1113 | ~v1_partfun1(B_1112, A_1113) | ~v4_relat_1(B_1112, A_1113) | ~v1_relat_1(B_1112))), inference(cnfTransformation, [status(thm)], [f_106])).
% 15.76/7.91  tff(c_25494, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1923, c_25485])).
% 15.76/7.91  tff(c_25503, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_25494])).
% 15.76/7.91  tff(c_25880, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_25503])).
% 15.76/7.91  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_236])).
% 15.76/7.91  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_236])).
% 15.76/7.91  tff(c_26116, plain, (![C_1163, A_1164, B_1165]: (v1_partfun1(C_1163, A_1164) | ~v1_funct_2(C_1163, A_1164, B_1165) | ~v1_funct_1(C_1163) | ~m1_subset_1(C_1163, k1_zfmisc_1(k2_zfmisc_1(A_1164, B_1165))) | v1_xboole_0(B_1165))), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.76/7.91  tff(c_26119, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_26116])).
% 15.76/7.91  tff(c_26129, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_26119])).
% 15.76/7.91  tff(c_26131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_25880, c_26129])).
% 15.76/7.91  tff(c_26132, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_25503])).
% 15.76/7.91  tff(c_14, plain, (![A_11, B_13]: (k7_relat_1(A_11, B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, k1_relat_1(A_11)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.76/7.91  tff(c_26140, plain, (![B_13]: (k7_relat_1('#skF_6', B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_26132, c_14])).
% 15.76/7.91  tff(c_26235, plain, (![B_1170]: (k7_relat_1('#skF_6', B_1170)=k1_xboole_0 | ~r1_xboole_0(B_1170, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_26140])).
% 15.76/7.91  tff(c_26239, plain, (![A_16]: (k7_relat_1('#skF_6', A_16)=k1_xboole_0 | ~r1_subset_1(A_16, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_20, c_26235])).
% 15.76/7.91  tff(c_26300, plain, (![A_1178]: (k7_relat_1('#skF_6', A_1178)=k1_xboole_0 | ~r1_subset_1(A_1178, '#skF_4') | v1_xboole_0(A_1178))), inference(negUnitSimplification, [status(thm)], [c_70, c_26239])).
% 15.76/7.91  tff(c_26303, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_26300])).
% 15.76/7.91  tff(c_26306, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_26303])).
% 15.76/7.91  tff(c_16, plain, (![B_15, A_14]: (k3_xboole_0(k1_relat_1(B_15), A_14)=k1_relat_1(k7_relat_1(B_15, A_14)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.76/7.91  tff(c_26143, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_6', A_14))=k3_xboole_0('#skF_4', A_14) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_26132, c_16])).
% 15.76/7.91  tff(c_26151, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_6', A_14))=k3_xboole_0('#skF_4', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_26143])).
% 15.76/7.91  tff(c_26310, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26306, c_26151])).
% 15.76/7.91  tff(c_25369, plain, (![B_1088, A_1089]: (r1_subset_1(B_1088, A_1089) | ~r1_subset_1(A_1089, B_1088) | v1_xboole_0(B_1088) | v1_xboole_0(A_1089))), inference(cnfTransformation, [status(thm)], [f_74])).
% 15.76/7.91  tff(c_25371, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_25369])).
% 15.76/7.91  tff(c_25374, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_74, c_70, c_25371])).
% 15.76/7.91  tff(c_25380, plain, (![A_1090, B_1091]: (r1_xboole_0(A_1090, B_1091) | ~r1_subset_1(A_1090, B_1091) | v1_xboole_0(B_1091) | v1_xboole_0(A_1090))), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.76/7.91  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.76/7.91  tff(c_26426, plain, (![A_1192, B_1193]: (k3_xboole_0(A_1192, B_1193)=k1_xboole_0 | ~r1_subset_1(A_1192, B_1193) | v1_xboole_0(B_1193) | v1_xboole_0(A_1192))), inference(resolution, [status(thm)], [c_25380, c_2])).
% 15.76/7.91  tff(c_26429, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_25374, c_26426])).
% 15.76/7.91  tff(c_26434, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26310, c_26429])).
% 15.76/7.91  tff(c_26435, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_74, c_26434])).
% 15.76/7.91  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.76/7.91  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.76/7.91  tff(c_10, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.76/7.91  tff(c_106, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_93])).
% 15.76/7.91  tff(c_26451, plain, (![B_13]: (k7_relat_1(k1_xboole_0, B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26435, c_14])).
% 15.76/7.91  tff(c_26498, plain, (![B_1204]: (k7_relat_1(k1_xboole_0, B_1204)=k1_xboole_0 | ~r1_xboole_0(B_1204, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_26451])).
% 15.76/7.91  tff(c_26506, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0 | k3_xboole_0(A_1, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_26498])).
% 15.76/7.91  tff(c_26510, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_26506])).
% 15.76/7.91  tff(c_26454, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26435, c_16])).
% 15.76/7.91  tff(c_26462, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_26454])).
% 15.76/7.91  tff(c_26525, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26435, c_26510, c_26462])).
% 15.76/7.91  tff(c_26319, plain, (![A_1179]: (k7_relat_1('#skF_6', A_1179)=k1_xboole_0 | k3_xboole_0(A_1179, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_26235])).
% 15.76/7.91  tff(c_1926, plain, (![B_432, A_433]: (k3_xboole_0(k1_relat_1(B_432), A_433)=k1_relat_1(k7_relat_1(B_432, A_433)) | ~v1_relat_1(B_432))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.76/7.91  tff(c_1933, plain, (![B_432]: (k1_relat_1(k7_relat_1(B_432, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_432))), inference(superposition, [status(thm), theory('equality')], [c_1926, c_6])).
% 15.76/7.91  tff(c_26332, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1('#skF_6') | k3_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26319, c_1933])).
% 15.76/7.91  tff(c_26342, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_104, c_26332])).
% 15.76/7.91  tff(c_26365, plain, (k3_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_26342])).
% 15.76/7.91  tff(c_26530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26525, c_26365])).
% 15.76/7.91  tff(c_26531, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_26342])).
% 15.76/7.91  tff(c_26549, plain, (![B_13]: (k7_relat_1(k1_xboole_0, B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26531, c_14])).
% 15.76/7.91  tff(c_26631, plain, (![B_1217]: (k7_relat_1(k1_xboole_0, B_1217)=k1_xboole_0 | ~r1_xboole_0(B_1217, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_26549])).
% 15.76/7.91  tff(c_26639, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0 | k3_xboole_0(A_1, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_26631])).
% 15.76/7.91  tff(c_26643, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_26639])).
% 15.76/7.91  tff(c_26552, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26531, c_16])).
% 15.76/7.91  tff(c_26560, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_26552])).
% 15.76/7.91  tff(c_26658, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26531, c_26643, c_26560])).
% 15.76/7.91  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_236])).
% 15.76/7.91  tff(c_105, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_93])).
% 15.76/7.91  tff(c_1924, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_1912])).
% 15.76/7.91  tff(c_25488, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1924, c_25485])).
% 15.76/7.91  tff(c_25497, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_25488])).
% 15.76/7.91  tff(c_25504, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_25497])).
% 15.76/7.91  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_236])).
% 15.76/7.91  tff(c_62, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_236])).
% 15.76/7.91  tff(c_25834, plain, (![C_1143, A_1144, B_1145]: (v1_partfun1(C_1143, A_1144) | ~v1_funct_2(C_1143, A_1144, B_1145) | ~v1_funct_1(C_1143) | ~m1_subset_1(C_1143, k1_zfmisc_1(k2_zfmisc_1(A_1144, B_1145))) | v1_xboole_0(B_1145))), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.76/7.91  tff(c_25840, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_25834])).
% 15.76/7.91  tff(c_25851, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_25840])).
% 15.76/7.91  tff(c_25853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_25504, c_25851])).
% 15.76/7.91  tff(c_25854, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_25497])).
% 15.76/7.91  tff(c_25862, plain, (![B_13]: (k7_relat_1('#skF_5', B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_25854, c_14])).
% 15.76/7.91  tff(c_26222, plain, (![B_1169]: (k7_relat_1('#skF_5', B_1169)=k1_xboole_0 | ~r1_xboole_0(B_1169, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_25862])).
% 15.76/7.91  tff(c_26282, plain, (![A_1177]: (k7_relat_1('#skF_5', A_1177)=k1_xboole_0 | k3_xboole_0(A_1177, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_26222])).
% 15.76/7.91  tff(c_26292, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1('#skF_5') | k3_xboole_0(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26282, c_1933])).
% 15.76/7.91  tff(c_26298, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_105, c_26292])).
% 15.76/7.91  tff(c_26318, plain, (k3_xboole_0(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_26298])).
% 15.76/7.91  tff(c_26662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26658, c_26318])).
% 15.76/7.91  tff(c_26663, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_26298])).
% 15.76/7.91  tff(c_26674, plain, (![B_13]: (k7_relat_1(k1_xboole_0, B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26663, c_14])).
% 15.76/7.91  tff(c_26753, plain, (![B_1224]: (k7_relat_1(k1_xboole_0, B_1224)=k1_xboole_0 | ~r1_xboole_0(B_1224, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_26674])).
% 15.76/7.91  tff(c_26761, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0 | k3_xboole_0(A_1, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_26753])).
% 15.76/7.91  tff(c_26765, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_26761])).
% 15.76/7.91  tff(c_26677, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26663, c_16])).
% 15.76/7.91  tff(c_26685, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_26677])).
% 15.76/7.91  tff(c_26797, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26663, c_26765, c_26685])).
% 15.76/7.91  tff(c_25349, plain, (![A_1085, B_1086]: (k7_relat_1(A_1085, B_1086)=k1_xboole_0 | ~r1_xboole_0(B_1086, k1_relat_1(A_1085)) | ~v1_relat_1(A_1085))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.76/7.91  tff(c_26925, plain, (![A_1249, A_1250]: (k7_relat_1(A_1249, A_1250)=k1_xboole_0 | ~v1_relat_1(A_1249) | k3_xboole_0(A_1250, k1_relat_1(A_1249))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_25349])).
% 15.76/7.91  tff(c_26961, plain, (![A_1251]: (k7_relat_1(A_1251, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_1251))), inference(superposition, [status(thm), theory('equality')], [c_26797, c_26925])).
% 15.76/7.91  tff(c_26974, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_104, c_26961])).
% 15.76/7.91  tff(c_26973, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_105, c_26961])).
% 15.76/7.91  tff(c_26226, plain, (![A_16]: (k7_relat_1('#skF_5', A_16)=k1_xboole_0 | ~r1_subset_1(A_16, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_20, c_26222])).
% 15.76/7.91  tff(c_26716, plain, (![A_1222]: (k7_relat_1('#skF_5', A_1222)=k1_xboole_0 | ~r1_subset_1(A_1222, '#skF_3') | v1_xboole_0(A_1222))), inference(negUnitSimplification, [status(thm)], [c_74, c_26226])).
% 15.76/7.91  tff(c_26719, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_25374, c_26716])).
% 15.76/7.91  tff(c_26722, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_26719])).
% 15.76/7.91  tff(c_25865, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_5', A_14))=k3_xboole_0('#skF_3', A_14) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_25854, c_16])).
% 15.76/7.91  tff(c_25873, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_5', A_14))=k3_xboole_0('#skF_3', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_25865])).
% 15.76/7.91  tff(c_26729, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26722, c_25873])).
% 15.76/7.91  tff(c_26738, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26663, c_26729])).
% 15.76/7.91  tff(c_25423, plain, (![A_1102, B_1103, C_1104]: (k9_subset_1(A_1102, B_1103, C_1104)=k3_xboole_0(B_1103, C_1104) | ~m1_subset_1(C_1104, k1_zfmisc_1(A_1102)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.76/7.91  tff(c_25438, plain, (![B_1103]: (k9_subset_1('#skF_1', B_1103, '#skF_4')=k3_xboole_0(B_1103, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_25423])).
% 15.76/7.91  tff(c_26780, plain, (![F_1227, C_1228, A_1230, B_1229, E_1231, D_1226]: (v1_funct_1(k1_tmap_1(A_1230, B_1229, C_1228, D_1226, E_1231, F_1227)) | ~m1_subset_1(F_1227, k1_zfmisc_1(k2_zfmisc_1(D_1226, B_1229))) | ~v1_funct_2(F_1227, D_1226, B_1229) | ~v1_funct_1(F_1227) | ~m1_subset_1(E_1231, k1_zfmisc_1(k2_zfmisc_1(C_1228, B_1229))) | ~v1_funct_2(E_1231, C_1228, B_1229) | ~v1_funct_1(E_1231) | ~m1_subset_1(D_1226, k1_zfmisc_1(A_1230)) | v1_xboole_0(D_1226) | ~m1_subset_1(C_1228, k1_zfmisc_1(A_1230)) | v1_xboole_0(C_1228) | v1_xboole_0(B_1229) | v1_xboole_0(A_1230))), inference(cnfTransformation, [status(thm)], [f_194])).
% 15.76/7.91  tff(c_26782, plain, (![A_1230, C_1228, E_1231]: (v1_funct_1(k1_tmap_1(A_1230, '#skF_2', C_1228, '#skF_4', E_1231, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1231, k1_zfmisc_1(k2_zfmisc_1(C_1228, '#skF_2'))) | ~v1_funct_2(E_1231, C_1228, '#skF_2') | ~v1_funct_1(E_1231) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1230)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1228, k1_zfmisc_1(A_1230)) | v1_xboole_0(C_1228) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1230))), inference(resolution, [status(thm)], [c_54, c_26780])).
% 15.76/7.91  tff(c_26790, plain, (![A_1230, C_1228, E_1231]: (v1_funct_1(k1_tmap_1(A_1230, '#skF_2', C_1228, '#skF_4', E_1231, '#skF_6')) | ~m1_subset_1(E_1231, k1_zfmisc_1(k2_zfmisc_1(C_1228, '#skF_2'))) | ~v1_funct_2(E_1231, C_1228, '#skF_2') | ~v1_funct_1(E_1231) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1230)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1228, k1_zfmisc_1(A_1230)) | v1_xboole_0(C_1228) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1230))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_26782])).
% 15.76/7.91  tff(c_26858, plain, (![A_1235, C_1236, E_1237]: (v1_funct_1(k1_tmap_1(A_1235, '#skF_2', C_1236, '#skF_4', E_1237, '#skF_6')) | ~m1_subset_1(E_1237, k1_zfmisc_1(k2_zfmisc_1(C_1236, '#skF_2'))) | ~v1_funct_2(E_1237, C_1236, '#skF_2') | ~v1_funct_1(E_1237) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1235)) | ~m1_subset_1(C_1236, k1_zfmisc_1(A_1235)) | v1_xboole_0(C_1236) | v1_xboole_0(A_1235))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_26790])).
% 15.76/7.91  tff(c_26862, plain, (![A_1235]: (v1_funct_1(k1_tmap_1(A_1235, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1235)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1235)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1235))), inference(resolution, [status(thm)], [c_60, c_26858])).
% 15.76/7.91  tff(c_26872, plain, (![A_1235]: (v1_funct_1(k1_tmap_1(A_1235, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1235)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1235)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1235))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_26862])).
% 15.76/7.91  tff(c_27161, plain, (![A_1271]: (v1_funct_1(k1_tmap_1(A_1271, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1271)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1271)) | v1_xboole_0(A_1271))), inference(negUnitSimplification, [status(thm)], [c_74, c_26872])).
% 15.76/7.91  tff(c_27164, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_27161])).
% 15.76/7.91  tff(c_27167, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_27164])).
% 15.76/7.91  tff(c_27168, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_27167])).
% 15.76/7.91  tff(c_26248, plain, (![A_1171, B_1172, C_1173, D_1174]: (k2_partfun1(A_1171, B_1172, C_1173, D_1174)=k7_relat_1(C_1173, D_1174) | ~m1_subset_1(C_1173, k1_zfmisc_1(k2_zfmisc_1(A_1171, B_1172))) | ~v1_funct_1(C_1173))), inference(cnfTransformation, [status(thm)], [f_112])).
% 15.76/7.91  tff(c_26252, plain, (![D_1174]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1174)=k7_relat_1('#skF_5', D_1174) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_26248])).
% 15.76/7.91  tff(c_26261, plain, (![D_1174]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1174)=k7_relat_1('#skF_5', D_1174))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_26252])).
% 15.76/7.91  tff(c_26250, plain, (![D_1174]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1174)=k7_relat_1('#skF_6', D_1174) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_26248])).
% 15.76/7.91  tff(c_26258, plain, (![D_1174]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1174)=k7_relat_1('#skF_6', D_1174))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_26250])).
% 15.76/7.91  tff(c_48, plain, (![A_163, C_165, D_166, F_168, B_164, E_167]: (v1_funct_2(k1_tmap_1(A_163, B_164, C_165, D_166, E_167, F_168), k4_subset_1(A_163, C_165, D_166), B_164) | ~m1_subset_1(F_168, k1_zfmisc_1(k2_zfmisc_1(D_166, B_164))) | ~v1_funct_2(F_168, D_166, B_164) | ~v1_funct_1(F_168) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(C_165, B_164))) | ~v1_funct_2(E_167, C_165, B_164) | ~v1_funct_1(E_167) | ~m1_subset_1(D_166, k1_zfmisc_1(A_163)) | v1_xboole_0(D_166) | ~m1_subset_1(C_165, k1_zfmisc_1(A_163)) | v1_xboole_0(C_165) | v1_xboole_0(B_164) | v1_xboole_0(A_163))), inference(cnfTransformation, [status(thm)], [f_194])).
% 15.76/7.91  tff(c_46, plain, (![A_163, C_165, D_166, F_168, B_164, E_167]: (m1_subset_1(k1_tmap_1(A_163, B_164, C_165, D_166, E_167, F_168), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_163, C_165, D_166), B_164))) | ~m1_subset_1(F_168, k1_zfmisc_1(k2_zfmisc_1(D_166, B_164))) | ~v1_funct_2(F_168, D_166, B_164) | ~v1_funct_1(F_168) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(C_165, B_164))) | ~v1_funct_2(E_167, C_165, B_164) | ~v1_funct_1(E_167) | ~m1_subset_1(D_166, k1_zfmisc_1(A_163)) | v1_xboole_0(D_166) | ~m1_subset_1(C_165, k1_zfmisc_1(A_163)) | v1_xboole_0(C_165) | v1_xboole_0(B_164) | v1_xboole_0(A_163))), inference(cnfTransformation, [status(thm)], [f_194])).
% 15.76/7.91  tff(c_27131, plain, (![A_1266, B_1265, F_1268, E_1267, D_1264, C_1263]: (k2_partfun1(k4_subset_1(A_1266, C_1263, D_1264), B_1265, k1_tmap_1(A_1266, B_1265, C_1263, D_1264, E_1267, F_1268), C_1263)=E_1267 | ~m1_subset_1(k1_tmap_1(A_1266, B_1265, C_1263, D_1264, E_1267, F_1268), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1266, C_1263, D_1264), B_1265))) | ~v1_funct_2(k1_tmap_1(A_1266, B_1265, C_1263, D_1264, E_1267, F_1268), k4_subset_1(A_1266, C_1263, D_1264), B_1265) | ~v1_funct_1(k1_tmap_1(A_1266, B_1265, C_1263, D_1264, E_1267, F_1268)) | k2_partfun1(D_1264, B_1265, F_1268, k9_subset_1(A_1266, C_1263, D_1264))!=k2_partfun1(C_1263, B_1265, E_1267, k9_subset_1(A_1266, C_1263, D_1264)) | ~m1_subset_1(F_1268, k1_zfmisc_1(k2_zfmisc_1(D_1264, B_1265))) | ~v1_funct_2(F_1268, D_1264, B_1265) | ~v1_funct_1(F_1268) | ~m1_subset_1(E_1267, k1_zfmisc_1(k2_zfmisc_1(C_1263, B_1265))) | ~v1_funct_2(E_1267, C_1263, B_1265) | ~v1_funct_1(E_1267) | ~m1_subset_1(D_1264, k1_zfmisc_1(A_1266)) | v1_xboole_0(D_1264) | ~m1_subset_1(C_1263, k1_zfmisc_1(A_1266)) | v1_xboole_0(C_1263) | v1_xboole_0(B_1265) | v1_xboole_0(A_1266))), inference(cnfTransformation, [status(thm)], [f_160])).
% 15.76/7.91  tff(c_33127, plain, (![B_1470, F_1468, D_1467, C_1469, A_1471, E_1472]: (k2_partfun1(k4_subset_1(A_1471, C_1469, D_1467), B_1470, k1_tmap_1(A_1471, B_1470, C_1469, D_1467, E_1472, F_1468), C_1469)=E_1472 | ~v1_funct_2(k1_tmap_1(A_1471, B_1470, C_1469, D_1467, E_1472, F_1468), k4_subset_1(A_1471, C_1469, D_1467), B_1470) | ~v1_funct_1(k1_tmap_1(A_1471, B_1470, C_1469, D_1467, E_1472, F_1468)) | k2_partfun1(D_1467, B_1470, F_1468, k9_subset_1(A_1471, C_1469, D_1467))!=k2_partfun1(C_1469, B_1470, E_1472, k9_subset_1(A_1471, C_1469, D_1467)) | ~m1_subset_1(F_1468, k1_zfmisc_1(k2_zfmisc_1(D_1467, B_1470))) | ~v1_funct_2(F_1468, D_1467, B_1470) | ~v1_funct_1(F_1468) | ~m1_subset_1(E_1472, k1_zfmisc_1(k2_zfmisc_1(C_1469, B_1470))) | ~v1_funct_2(E_1472, C_1469, B_1470) | ~v1_funct_1(E_1472) | ~m1_subset_1(D_1467, k1_zfmisc_1(A_1471)) | v1_xboole_0(D_1467) | ~m1_subset_1(C_1469, k1_zfmisc_1(A_1471)) | v1_xboole_0(C_1469) | v1_xboole_0(B_1470) | v1_xboole_0(A_1471))), inference(resolution, [status(thm)], [c_46, c_27131])).
% 15.76/7.91  tff(c_39175, plain, (![A_1570, D_1566, E_1571, C_1568, F_1567, B_1569]: (k2_partfun1(k4_subset_1(A_1570, C_1568, D_1566), B_1569, k1_tmap_1(A_1570, B_1569, C_1568, D_1566, E_1571, F_1567), C_1568)=E_1571 | ~v1_funct_1(k1_tmap_1(A_1570, B_1569, C_1568, D_1566, E_1571, F_1567)) | k2_partfun1(D_1566, B_1569, F_1567, k9_subset_1(A_1570, C_1568, D_1566))!=k2_partfun1(C_1568, B_1569, E_1571, k9_subset_1(A_1570, C_1568, D_1566)) | ~m1_subset_1(F_1567, k1_zfmisc_1(k2_zfmisc_1(D_1566, B_1569))) | ~v1_funct_2(F_1567, D_1566, B_1569) | ~v1_funct_1(F_1567) | ~m1_subset_1(E_1571, k1_zfmisc_1(k2_zfmisc_1(C_1568, B_1569))) | ~v1_funct_2(E_1571, C_1568, B_1569) | ~v1_funct_1(E_1571) | ~m1_subset_1(D_1566, k1_zfmisc_1(A_1570)) | v1_xboole_0(D_1566) | ~m1_subset_1(C_1568, k1_zfmisc_1(A_1570)) | v1_xboole_0(C_1568) | v1_xboole_0(B_1569) | v1_xboole_0(A_1570))), inference(resolution, [status(thm)], [c_48, c_33127])).
% 15.76/7.91  tff(c_39179, plain, (![A_1570, C_1568, E_1571]: (k2_partfun1(k4_subset_1(A_1570, C_1568, '#skF_4'), '#skF_2', k1_tmap_1(A_1570, '#skF_2', C_1568, '#skF_4', E_1571, '#skF_6'), C_1568)=E_1571 | ~v1_funct_1(k1_tmap_1(A_1570, '#skF_2', C_1568, '#skF_4', E_1571, '#skF_6')) | k2_partfun1(C_1568, '#skF_2', E_1571, k9_subset_1(A_1570, C_1568, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1570, C_1568, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1571, k1_zfmisc_1(k2_zfmisc_1(C_1568, '#skF_2'))) | ~v1_funct_2(E_1571, C_1568, '#skF_2') | ~v1_funct_1(E_1571) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1570)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1568, k1_zfmisc_1(A_1570)) | v1_xboole_0(C_1568) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1570))), inference(resolution, [status(thm)], [c_54, c_39175])).
% 15.76/7.91  tff(c_39188, plain, (![A_1570, C_1568, E_1571]: (k2_partfun1(k4_subset_1(A_1570, C_1568, '#skF_4'), '#skF_2', k1_tmap_1(A_1570, '#skF_2', C_1568, '#skF_4', E_1571, '#skF_6'), C_1568)=E_1571 | ~v1_funct_1(k1_tmap_1(A_1570, '#skF_2', C_1568, '#skF_4', E_1571, '#skF_6')) | k2_partfun1(C_1568, '#skF_2', E_1571, k9_subset_1(A_1570, C_1568, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1570, C_1568, '#skF_4')) | ~m1_subset_1(E_1571, k1_zfmisc_1(k2_zfmisc_1(C_1568, '#skF_2'))) | ~v1_funct_2(E_1571, C_1568, '#skF_2') | ~v1_funct_1(E_1571) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1570)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1568, k1_zfmisc_1(A_1570)) | v1_xboole_0(C_1568) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1570))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_26258, c_39179])).
% 15.76/7.91  tff(c_39228, plain, (![A_1580, C_1581, E_1582]: (k2_partfun1(k4_subset_1(A_1580, C_1581, '#skF_4'), '#skF_2', k1_tmap_1(A_1580, '#skF_2', C_1581, '#skF_4', E_1582, '#skF_6'), C_1581)=E_1582 | ~v1_funct_1(k1_tmap_1(A_1580, '#skF_2', C_1581, '#skF_4', E_1582, '#skF_6')) | k2_partfun1(C_1581, '#skF_2', E_1582, k9_subset_1(A_1580, C_1581, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1580, C_1581, '#skF_4')) | ~m1_subset_1(E_1582, k1_zfmisc_1(k2_zfmisc_1(C_1581, '#skF_2'))) | ~v1_funct_2(E_1582, C_1581, '#skF_2') | ~v1_funct_1(E_1582) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1580)) | ~m1_subset_1(C_1581, k1_zfmisc_1(A_1580)) | v1_xboole_0(C_1581) | v1_xboole_0(A_1580))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_39188])).
% 15.76/7.91  tff(c_39235, plain, (![A_1580]: (k2_partfun1(k4_subset_1(A_1580, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1580, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1580, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1580, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1580, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1580)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1580)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1580))), inference(resolution, [status(thm)], [c_60, c_39228])).
% 15.76/7.91  tff(c_39248, plain, (![A_1580]: (k2_partfun1(k4_subset_1(A_1580, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1580, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1580, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1580, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1580, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1580)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1580)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1580))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_26261, c_39235])).
% 15.76/7.91  tff(c_47616, plain, (![A_1695]: (k2_partfun1(k4_subset_1(A_1695, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1695, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1695, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1695, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1695, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1695)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1695)) | v1_xboole_0(A_1695))), inference(negUnitSimplification, [status(thm)], [c_74, c_39248])).
% 15.76/7.91  tff(c_2028, plain, (![B_454, A_455]: (k1_relat_1(B_454)=A_455 | ~v1_partfun1(B_454, A_455) | ~v4_relat_1(B_454, A_455) | ~v1_relat_1(B_454))), inference(cnfTransformation, [status(thm)], [f_106])).
% 15.76/7.91  tff(c_2037, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1923, c_2028])).
% 15.76/7.91  tff(c_2046, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_2037])).
% 15.76/7.91  tff(c_2531, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_2046])).
% 15.76/7.91  tff(c_2762, plain, (![C_529, A_530, B_531]: (v1_partfun1(C_529, A_530) | ~v1_funct_2(C_529, A_530, B_531) | ~v1_funct_1(C_529) | ~m1_subset_1(C_529, k1_zfmisc_1(k2_zfmisc_1(A_530, B_531))) | v1_xboole_0(B_531))), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.76/7.91  tff(c_2765, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_2762])).
% 15.76/7.91  tff(c_2775, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2765])).
% 15.76/7.91  tff(c_2777, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_2531, c_2775])).
% 15.76/7.91  tff(c_2778, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_2046])).
% 15.76/7.91  tff(c_2786, plain, (![B_13]: (k7_relat_1('#skF_6', B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2778, c_14])).
% 15.76/7.91  tff(c_2837, plain, (![B_534]: (k7_relat_1('#skF_6', B_534)=k1_xboole_0 | ~r1_xboole_0(B_534, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_2786])).
% 15.76/7.91  tff(c_2841, plain, (![A_16]: (k7_relat_1('#skF_6', A_16)=k1_xboole_0 | ~r1_subset_1(A_16, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_20, c_2837])).
% 15.76/7.91  tff(c_3026, plain, (![A_554]: (k7_relat_1('#skF_6', A_554)=k1_xboole_0 | ~r1_subset_1(A_554, '#skF_4') | v1_xboole_0(A_554))), inference(negUnitSimplification, [status(thm)], [c_70, c_2841])).
% 15.76/7.91  tff(c_3029, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_3026])).
% 15.76/7.91  tff(c_3032, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_3029])).
% 15.76/7.91  tff(c_2789, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_6', A_14))=k3_xboole_0('#skF_4', A_14) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2778, c_16])).
% 15.76/7.91  tff(c_2797, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_6', A_14))=k3_xboole_0('#skF_4', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_2789])).
% 15.76/7.91  tff(c_3039, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3032, c_2797])).
% 15.76/7.91  tff(c_1977, plain, (![B_439, A_440]: (r1_subset_1(B_439, A_440) | ~r1_subset_1(A_440, B_439) | v1_xboole_0(B_439) | v1_xboole_0(A_440))), inference(cnfTransformation, [status(thm)], [f_74])).
% 15.76/7.91  tff(c_1979, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1977])).
% 15.76/7.91  tff(c_1982, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_74, c_70, c_1979])).
% 15.76/7.91  tff(c_1988, plain, (![A_441, B_442]: (r1_xboole_0(A_441, B_442) | ~r1_subset_1(A_441, B_442) | v1_xboole_0(B_442) | v1_xboole_0(A_441))), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.76/7.91  tff(c_3157, plain, (![A_567, B_568]: (k3_xboole_0(A_567, B_568)=k1_xboole_0 | ~r1_subset_1(A_567, B_568) | v1_xboole_0(B_568) | v1_xboole_0(A_567))), inference(resolution, [status(thm)], [c_1988, c_2])).
% 15.76/7.91  tff(c_3160, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1982, c_3157])).
% 15.76/7.91  tff(c_3165, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3039, c_3160])).
% 15.76/7.91  tff(c_3166, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_74, c_3165])).
% 15.76/7.91  tff(c_3186, plain, (![B_13]: (k7_relat_1(k1_xboole_0, B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3166, c_14])).
% 15.76/7.91  tff(c_3267, plain, (![B_577]: (k7_relat_1(k1_xboole_0, B_577)=k1_xboole_0 | ~r1_xboole_0(B_577, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3186])).
% 15.76/7.91  tff(c_3275, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0 | k3_xboole_0(A_1, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_3267])).
% 15.76/7.91  tff(c_3279, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3275])).
% 15.76/7.91  tff(c_3189, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3166, c_16])).
% 15.76/7.91  tff(c_3197, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3189])).
% 15.76/7.91  tff(c_3298, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_3279, c_3197])).
% 15.76/7.91  tff(c_3299, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3166, c_3298])).
% 15.76/7.91  tff(c_2031, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1924, c_2028])).
% 15.76/7.91  tff(c_2040, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_2031])).
% 15.76/7.91  tff(c_2047, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_2040])).
% 15.76/7.91  tff(c_2489, plain, (![C_503, A_504, B_505]: (v1_partfun1(C_503, A_504) | ~v1_funct_2(C_503, A_504, B_505) | ~v1_funct_1(C_503) | ~m1_subset_1(C_503, k1_zfmisc_1(k2_zfmisc_1(A_504, B_505))) | v1_xboole_0(B_505))), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.76/7.91  tff(c_2495, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_2489])).
% 15.76/7.91  tff(c_2506, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2495])).
% 15.76/7.91  tff(c_2508, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_2047, c_2506])).
% 15.76/7.91  tff(c_2509, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_2040])).
% 15.76/7.91  tff(c_2517, plain, (![B_13]: (k7_relat_1('#skF_5', B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2509, c_14])).
% 15.76/7.91  tff(c_2850, plain, (![B_535]: (k7_relat_1('#skF_5', B_535)=k1_xboole_0 | ~r1_xboole_0(B_535, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_2517])).
% 15.76/7.91  tff(c_2965, plain, (![A_546]: (k7_relat_1('#skF_5', A_546)=k1_xboole_0 | k3_xboole_0(A_546, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2850])).
% 15.76/7.91  tff(c_2975, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1('#skF_5') | k3_xboole_0(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2965, c_1933])).
% 15.76/7.91  tff(c_2981, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_105, c_2975])).
% 15.76/7.91  tff(c_2983, plain, (k3_xboole_0(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2981])).
% 15.76/7.91  tff(c_3317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3299, c_2983])).
% 15.76/7.91  tff(c_3318, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_2981])).
% 15.76/7.91  tff(c_3328, plain, (![B_13]: (k7_relat_1(k1_xboole_0, B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3318, c_14])).
% 15.76/7.91  tff(c_3407, plain, (![B_589]: (k7_relat_1(k1_xboole_0, B_589)=k1_xboole_0 | ~r1_xboole_0(B_589, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3328])).
% 15.76/7.91  tff(c_3415, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0 | k3_xboole_0(A_1, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_3407])).
% 15.76/7.91  tff(c_3419, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3415])).
% 15.76/7.91  tff(c_3331, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3318, c_16])).
% 15.76/7.91  tff(c_3339, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3331])).
% 15.76/7.91  tff(c_3421, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_3419, c_3339])).
% 15.76/7.91  tff(c_3422, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3318, c_3421])).
% 15.76/7.91  tff(c_2894, plain, (![A_537]: (k7_relat_1('#skF_6', A_537)=k1_xboole_0 | k3_xboole_0(A_537, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2837])).
% 15.76/7.91  tff(c_2904, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1('#skF_6') | k3_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2894, c_1933])).
% 15.76/7.91  tff(c_2910, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_104, c_2904])).
% 15.76/7.91  tff(c_2964, plain, (k3_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2910])).
% 15.76/7.91  tff(c_3439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3422, c_2964])).
% 15.76/7.91  tff(c_3440, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_2910])).
% 15.76/7.91  tff(c_3450, plain, (![B_13]: (k7_relat_1(k1_xboole_0, B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3440, c_14])).
% 15.76/7.91  tff(c_3529, plain, (![B_598]: (k7_relat_1(k1_xboole_0, B_598)=k1_xboole_0 | ~r1_xboole_0(B_598, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3450])).
% 15.76/7.91  tff(c_3537, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0 | k3_xboole_0(A_1, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_3529])).
% 15.76/7.91  tff(c_3541, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3537])).
% 15.76/7.91  tff(c_3453, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3440, c_16])).
% 15.76/7.91  tff(c_3461, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3453])).
% 15.76/7.91  tff(c_3543, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_3541, c_3461])).
% 15.76/7.91  tff(c_3544, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3440, c_3543])).
% 15.76/7.91  tff(c_1957, plain, (![A_436, B_437]: (k7_relat_1(A_436, B_437)=k1_xboole_0 | ~r1_xboole_0(B_437, k1_relat_1(A_436)) | ~v1_relat_1(A_436))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.76/7.91  tff(c_3785, plain, (![A_624, A_625]: (k7_relat_1(A_624, A_625)=k1_xboole_0 | ~v1_relat_1(A_624) | k3_xboole_0(A_625, k1_relat_1(A_624))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1957])).
% 15.76/7.91  tff(c_3821, plain, (![A_626]: (k7_relat_1(A_626, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_626))), inference(superposition, [status(thm), theory('equality')], [c_3544, c_3785])).
% 15.76/7.91  tff(c_3834, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_104, c_3821])).
% 15.76/7.91  tff(c_3833, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_105, c_3821])).
% 15.76/7.91  tff(c_2854, plain, (![A_16]: (k7_relat_1('#skF_5', A_16)=k1_xboole_0 | ~r1_subset_1(A_16, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_20, c_2850])).
% 15.76/7.91  tff(c_3640, plain, (![A_608]: (k7_relat_1('#skF_5', A_608)=k1_xboole_0 | ~r1_subset_1(A_608, '#skF_3') | v1_xboole_0(A_608))), inference(negUnitSimplification, [status(thm)], [c_74, c_2854])).
% 15.76/7.91  tff(c_3643, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1982, c_3640])).
% 15.76/7.91  tff(c_3646, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_3643])).
% 15.76/7.91  tff(c_2520, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_5', A_14))=k3_xboole_0('#skF_3', A_14) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2509, c_16])).
% 15.76/7.91  tff(c_2528, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_5', A_14))=k3_xboole_0('#skF_3', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_2520])).
% 15.76/7.91  tff(c_3653, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3646, c_2528])).
% 15.76/7.91  tff(c_3660, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3440, c_3653])).
% 15.76/7.91  tff(c_2912, plain, (![A_538, B_539, C_540]: (k9_subset_1(A_538, B_539, C_540)=k3_xboole_0(B_539, C_540) | ~m1_subset_1(C_540, k1_zfmisc_1(A_538)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.76/7.91  tff(c_2927, plain, (![B_539]: (k9_subset_1('#skF_1', B_539, '#skF_4')=k3_xboole_0(B_539, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_2912])).
% 15.76/7.91  tff(c_3702, plain, (![C_612, E_615, A_614, B_613, F_611, D_610]: (v1_funct_1(k1_tmap_1(A_614, B_613, C_612, D_610, E_615, F_611)) | ~m1_subset_1(F_611, k1_zfmisc_1(k2_zfmisc_1(D_610, B_613))) | ~v1_funct_2(F_611, D_610, B_613) | ~v1_funct_1(F_611) | ~m1_subset_1(E_615, k1_zfmisc_1(k2_zfmisc_1(C_612, B_613))) | ~v1_funct_2(E_615, C_612, B_613) | ~v1_funct_1(E_615) | ~m1_subset_1(D_610, k1_zfmisc_1(A_614)) | v1_xboole_0(D_610) | ~m1_subset_1(C_612, k1_zfmisc_1(A_614)) | v1_xboole_0(C_612) | v1_xboole_0(B_613) | v1_xboole_0(A_614))), inference(cnfTransformation, [status(thm)], [f_194])).
% 15.76/7.91  tff(c_3704, plain, (![A_614, C_612, E_615]: (v1_funct_1(k1_tmap_1(A_614, '#skF_2', C_612, '#skF_4', E_615, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_615, k1_zfmisc_1(k2_zfmisc_1(C_612, '#skF_2'))) | ~v1_funct_2(E_615, C_612, '#skF_2') | ~v1_funct_1(E_615) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_614)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_612, k1_zfmisc_1(A_614)) | v1_xboole_0(C_612) | v1_xboole_0('#skF_2') | v1_xboole_0(A_614))), inference(resolution, [status(thm)], [c_54, c_3702])).
% 15.76/7.91  tff(c_3712, plain, (![A_614, C_612, E_615]: (v1_funct_1(k1_tmap_1(A_614, '#skF_2', C_612, '#skF_4', E_615, '#skF_6')) | ~m1_subset_1(E_615, k1_zfmisc_1(k2_zfmisc_1(C_612, '#skF_2'))) | ~v1_funct_2(E_615, C_612, '#skF_2') | ~v1_funct_1(E_615) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_614)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_612, k1_zfmisc_1(A_614)) | v1_xboole_0(C_612) | v1_xboole_0('#skF_2') | v1_xboole_0(A_614))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_3704])).
% 15.76/7.91  tff(c_5219, plain, (![A_699, C_700, E_701]: (v1_funct_1(k1_tmap_1(A_699, '#skF_2', C_700, '#skF_4', E_701, '#skF_6')) | ~m1_subset_1(E_701, k1_zfmisc_1(k2_zfmisc_1(C_700, '#skF_2'))) | ~v1_funct_2(E_701, C_700, '#skF_2') | ~v1_funct_1(E_701) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_699)) | ~m1_subset_1(C_700, k1_zfmisc_1(A_699)) | v1_xboole_0(C_700) | v1_xboole_0(A_699))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_3712])).
% 15.76/7.91  tff(c_5226, plain, (![A_699]: (v1_funct_1(k1_tmap_1(A_699, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_699)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_699)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_699))), inference(resolution, [status(thm)], [c_60, c_5219])).
% 15.76/7.91  tff(c_5239, plain, (![A_699]: (v1_funct_1(k1_tmap_1(A_699, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_699)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_699)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_699))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_5226])).
% 15.76/7.91  tff(c_5898, plain, (![A_716]: (v1_funct_1(k1_tmap_1(A_716, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_716)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_716)) | v1_xboole_0(A_716))), inference(negUnitSimplification, [status(thm)], [c_74, c_5239])).
% 15.76/7.91  tff(c_5901, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_5898])).
% 15.76/7.91  tff(c_5904, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_5901])).
% 15.76/7.91  tff(c_5905, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_5904])).
% 15.76/7.91  tff(c_3463, plain, (![A_591, B_592, C_593, D_594]: (k2_partfun1(A_591, B_592, C_593, D_594)=k7_relat_1(C_593, D_594) | ~m1_subset_1(C_593, k1_zfmisc_1(k2_zfmisc_1(A_591, B_592))) | ~v1_funct_1(C_593))), inference(cnfTransformation, [status(thm)], [f_112])).
% 15.76/7.91  tff(c_3467, plain, (![D_594]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_594)=k7_relat_1('#skF_5', D_594) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_3463])).
% 15.76/7.91  tff(c_3476, plain, (![D_594]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_594)=k7_relat_1('#skF_5', D_594))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3467])).
% 15.76/7.91  tff(c_3465, plain, (![D_594]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_594)=k7_relat_1('#skF_6', D_594) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_3463])).
% 15.76/7.91  tff(c_3473, plain, (![D_594]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_594)=k7_relat_1('#skF_6', D_594))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3465])).
% 15.76/7.91  tff(c_4355, plain, (![A_667, F_669, B_666, D_665, E_668, C_664]: (k2_partfun1(k4_subset_1(A_667, C_664, D_665), B_666, k1_tmap_1(A_667, B_666, C_664, D_665, E_668, F_669), D_665)=F_669 | ~m1_subset_1(k1_tmap_1(A_667, B_666, C_664, D_665, E_668, F_669), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_667, C_664, D_665), B_666))) | ~v1_funct_2(k1_tmap_1(A_667, B_666, C_664, D_665, E_668, F_669), k4_subset_1(A_667, C_664, D_665), B_666) | ~v1_funct_1(k1_tmap_1(A_667, B_666, C_664, D_665, E_668, F_669)) | k2_partfun1(D_665, B_666, F_669, k9_subset_1(A_667, C_664, D_665))!=k2_partfun1(C_664, B_666, E_668, k9_subset_1(A_667, C_664, D_665)) | ~m1_subset_1(F_669, k1_zfmisc_1(k2_zfmisc_1(D_665, B_666))) | ~v1_funct_2(F_669, D_665, B_666) | ~v1_funct_1(F_669) | ~m1_subset_1(E_668, k1_zfmisc_1(k2_zfmisc_1(C_664, B_666))) | ~v1_funct_2(E_668, C_664, B_666) | ~v1_funct_1(E_668) | ~m1_subset_1(D_665, k1_zfmisc_1(A_667)) | v1_xboole_0(D_665) | ~m1_subset_1(C_664, k1_zfmisc_1(A_667)) | v1_xboole_0(C_664) | v1_xboole_0(B_666) | v1_xboole_0(A_667))), inference(cnfTransformation, [status(thm)], [f_160])).
% 15.76/7.91  tff(c_10116, plain, (![B_847, E_849, C_846, A_848, D_844, F_845]: (k2_partfun1(k4_subset_1(A_848, C_846, D_844), B_847, k1_tmap_1(A_848, B_847, C_846, D_844, E_849, F_845), D_844)=F_845 | ~v1_funct_2(k1_tmap_1(A_848, B_847, C_846, D_844, E_849, F_845), k4_subset_1(A_848, C_846, D_844), B_847) | ~v1_funct_1(k1_tmap_1(A_848, B_847, C_846, D_844, E_849, F_845)) | k2_partfun1(D_844, B_847, F_845, k9_subset_1(A_848, C_846, D_844))!=k2_partfun1(C_846, B_847, E_849, k9_subset_1(A_848, C_846, D_844)) | ~m1_subset_1(F_845, k1_zfmisc_1(k2_zfmisc_1(D_844, B_847))) | ~v1_funct_2(F_845, D_844, B_847) | ~v1_funct_1(F_845) | ~m1_subset_1(E_849, k1_zfmisc_1(k2_zfmisc_1(C_846, B_847))) | ~v1_funct_2(E_849, C_846, B_847) | ~v1_funct_1(E_849) | ~m1_subset_1(D_844, k1_zfmisc_1(A_848)) | v1_xboole_0(D_844) | ~m1_subset_1(C_846, k1_zfmisc_1(A_848)) | v1_xboole_0(C_846) | v1_xboole_0(B_847) | v1_xboole_0(A_848))), inference(resolution, [status(thm)], [c_46, c_4355])).
% 15.76/7.91  tff(c_16225, plain, (![E_953, C_950, D_948, A_952, B_951, F_949]: (k2_partfun1(k4_subset_1(A_952, C_950, D_948), B_951, k1_tmap_1(A_952, B_951, C_950, D_948, E_953, F_949), D_948)=F_949 | ~v1_funct_1(k1_tmap_1(A_952, B_951, C_950, D_948, E_953, F_949)) | k2_partfun1(D_948, B_951, F_949, k9_subset_1(A_952, C_950, D_948))!=k2_partfun1(C_950, B_951, E_953, k9_subset_1(A_952, C_950, D_948)) | ~m1_subset_1(F_949, k1_zfmisc_1(k2_zfmisc_1(D_948, B_951))) | ~v1_funct_2(F_949, D_948, B_951) | ~v1_funct_1(F_949) | ~m1_subset_1(E_953, k1_zfmisc_1(k2_zfmisc_1(C_950, B_951))) | ~v1_funct_2(E_953, C_950, B_951) | ~v1_funct_1(E_953) | ~m1_subset_1(D_948, k1_zfmisc_1(A_952)) | v1_xboole_0(D_948) | ~m1_subset_1(C_950, k1_zfmisc_1(A_952)) | v1_xboole_0(C_950) | v1_xboole_0(B_951) | v1_xboole_0(A_952))), inference(resolution, [status(thm)], [c_48, c_10116])).
% 15.76/7.91  tff(c_16229, plain, (![A_952, C_950, E_953]: (k2_partfun1(k4_subset_1(A_952, C_950, '#skF_4'), '#skF_2', k1_tmap_1(A_952, '#skF_2', C_950, '#skF_4', E_953, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_952, '#skF_2', C_950, '#skF_4', E_953, '#skF_6')) | k2_partfun1(C_950, '#skF_2', E_953, k9_subset_1(A_952, C_950, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_952, C_950, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_953, k1_zfmisc_1(k2_zfmisc_1(C_950, '#skF_2'))) | ~v1_funct_2(E_953, C_950, '#skF_2') | ~v1_funct_1(E_953) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_952)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_950, k1_zfmisc_1(A_952)) | v1_xboole_0(C_950) | v1_xboole_0('#skF_2') | v1_xboole_0(A_952))), inference(resolution, [status(thm)], [c_54, c_16225])).
% 15.76/7.91  tff(c_16238, plain, (![A_952, C_950, E_953]: (k2_partfun1(k4_subset_1(A_952, C_950, '#skF_4'), '#skF_2', k1_tmap_1(A_952, '#skF_2', C_950, '#skF_4', E_953, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_952, '#skF_2', C_950, '#skF_4', E_953, '#skF_6')) | k2_partfun1(C_950, '#skF_2', E_953, k9_subset_1(A_952, C_950, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_952, C_950, '#skF_4')) | ~m1_subset_1(E_953, k1_zfmisc_1(k2_zfmisc_1(C_950, '#skF_2'))) | ~v1_funct_2(E_953, C_950, '#skF_2') | ~v1_funct_1(E_953) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_952)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_950, k1_zfmisc_1(A_952)) | v1_xboole_0(C_950) | v1_xboole_0('#skF_2') | v1_xboole_0(A_952))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_3473, c_16229])).
% 15.76/7.91  tff(c_21181, plain, (![A_1045, C_1046, E_1047]: (k2_partfun1(k4_subset_1(A_1045, C_1046, '#skF_4'), '#skF_2', k1_tmap_1(A_1045, '#skF_2', C_1046, '#skF_4', E_1047, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1045, '#skF_2', C_1046, '#skF_4', E_1047, '#skF_6')) | k2_partfun1(C_1046, '#skF_2', E_1047, k9_subset_1(A_1045, C_1046, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1045, C_1046, '#skF_4')) | ~m1_subset_1(E_1047, k1_zfmisc_1(k2_zfmisc_1(C_1046, '#skF_2'))) | ~v1_funct_2(E_1047, C_1046, '#skF_2') | ~v1_funct_1(E_1047) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1045)) | ~m1_subset_1(C_1046, k1_zfmisc_1(A_1045)) | v1_xboole_0(C_1046) | v1_xboole_0(A_1045))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_16238])).
% 15.76/7.91  tff(c_21188, plain, (![A_1045]: (k2_partfun1(k4_subset_1(A_1045, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1045, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1045, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1045, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1045, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1045)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1045)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1045))), inference(resolution, [status(thm)], [c_60, c_21181])).
% 15.76/7.91  tff(c_21201, plain, (![A_1045]: (k2_partfun1(k4_subset_1(A_1045, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1045, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1045, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1045, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1045, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1045)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1045)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1045))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_3476, c_21188])).
% 15.76/7.91  tff(c_25307, plain, (![A_1083]: (k2_partfun1(k4_subset_1(A_1083, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1083, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1083, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1083, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1083, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1083)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1083)) | v1_xboole_0(A_1083))), inference(negUnitSimplification, [status(thm)], [c_74, c_21201])).
% 15.76/7.91  tff(c_122, plain, (![C_238, A_239, B_240]: (v4_relat_1(C_238, A_239) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.76/7.91  tff(c_133, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_122])).
% 15.76/7.91  tff(c_299, plain, (![B_273, A_274]: (k1_relat_1(B_273)=A_274 | ~v1_partfun1(B_273, A_274) | ~v4_relat_1(B_273, A_274) | ~v1_relat_1(B_273))), inference(cnfTransformation, [status(thm)], [f_106])).
% 15.76/7.91  tff(c_308, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_133, c_299])).
% 15.76/7.91  tff(c_317, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_308])).
% 15.76/7.91  tff(c_543, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_317])).
% 15.76/7.91  tff(c_597, plain, (![C_299, A_300, B_301]: (v1_partfun1(C_299, A_300) | ~v1_funct_2(C_299, A_300, B_301) | ~v1_funct_1(C_299) | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(A_300, B_301))) | v1_xboole_0(B_301))), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.76/7.91  tff(c_600, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_597])).
% 15.76/7.91  tff(c_610, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_600])).
% 15.76/7.91  tff(c_612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_543, c_610])).
% 15.76/7.91  tff(c_613, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_317])).
% 15.76/7.91  tff(c_624, plain, (![B_13]: (k7_relat_1('#skF_6', B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_613, c_14])).
% 15.76/7.91  tff(c_644, plain, (![B_303]: (k7_relat_1('#skF_6', B_303)=k1_xboole_0 | ~r1_xboole_0(B_303, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_624])).
% 15.76/7.91  tff(c_648, plain, (![A_16]: (k7_relat_1('#skF_6', A_16)=k1_xboole_0 | ~r1_subset_1(A_16, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_20, c_644])).
% 15.76/7.91  tff(c_816, plain, (![A_313]: (k7_relat_1('#skF_6', A_313)=k1_xboole_0 | ~r1_subset_1(A_313, '#skF_4') | v1_xboole_0(A_313))), inference(negUnitSimplification, [status(thm)], [c_70, c_648])).
% 15.76/7.91  tff(c_819, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_816])).
% 15.76/7.91  tff(c_822, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_819])).
% 15.76/7.91  tff(c_621, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_6', A_14))=k3_xboole_0('#skF_4', A_14) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_613, c_16])).
% 15.76/7.91  tff(c_630, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_6', A_14))=k3_xboole_0('#skF_4', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_621])).
% 15.76/7.91  tff(c_846, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_822, c_630])).
% 15.76/7.91  tff(c_202, plain, (![B_259, A_260]: (r1_subset_1(B_259, A_260) | ~r1_subset_1(A_260, B_259) | v1_xboole_0(B_259) | v1_xboole_0(A_260))), inference(cnfTransformation, [status(thm)], [f_74])).
% 15.76/7.91  tff(c_204, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_202])).
% 15.76/7.91  tff(c_207, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_74, c_70, c_204])).
% 15.76/7.91  tff(c_213, plain, (![A_261, B_262]: (r1_xboole_0(A_261, B_262) | ~r1_subset_1(A_261, B_262) | v1_xboole_0(B_262) | v1_xboole_0(A_261))), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.76/7.91  tff(c_893, plain, (![A_325, B_326]: (k3_xboole_0(A_325, B_326)=k1_xboole_0 | ~r1_subset_1(A_325, B_326) | v1_xboole_0(B_326) | v1_xboole_0(A_325))), inference(resolution, [status(thm)], [c_213, c_2])).
% 15.76/7.91  tff(c_896, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_207, c_893])).
% 15.76/7.91  tff(c_901, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_846, c_896])).
% 15.76/7.91  tff(c_902, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_74, c_901])).
% 15.76/7.91  tff(c_921, plain, (![B_13]: (k7_relat_1(k1_xboole_0, B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_902, c_14])).
% 15.76/7.91  tff(c_986, plain, (![B_336]: (k7_relat_1(k1_xboole_0, B_336)=k1_xboole_0 | ~r1_xboole_0(B_336, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_921])).
% 15.76/7.91  tff(c_994, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0 | k3_xboole_0(A_1, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_986])).
% 15.76/7.91  tff(c_998, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_994])).
% 15.76/7.91  tff(c_918, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_902, c_16])).
% 15.76/7.91  tff(c_927, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_918])).
% 15.76/7.91  tff(c_1035, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_998, c_927])).
% 15.76/7.91  tff(c_1036, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_902, c_1035])).
% 15.76/7.91  tff(c_134, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_122])).
% 15.76/7.91  tff(c_305, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_134, c_299])).
% 15.76/7.91  tff(c_314, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_305])).
% 15.76/7.91  tff(c_339, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_314])).
% 15.76/7.91  tff(c_492, plain, (![C_292, A_293, B_294]: (v1_partfun1(C_292, A_293) | ~v1_funct_2(C_292, A_293, B_294) | ~v1_funct_1(C_292) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))) | v1_xboole_0(B_294))), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.76/7.91  tff(c_498, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_492])).
% 15.76/7.91  tff(c_509, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_498])).
% 15.76/7.91  tff(c_511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_339, c_509])).
% 15.76/7.91  tff(c_512, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_314])).
% 15.76/7.91  tff(c_523, plain, (![B_13]: (k7_relat_1('#skF_5', B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_512, c_14])).
% 15.76/7.91  tff(c_688, plain, (![B_305]: (k7_relat_1('#skF_5', B_305)=k1_xboole_0 | ~r1_xboole_0(B_305, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_523])).
% 15.76/7.91  tff(c_771, plain, (![A_311]: (k7_relat_1('#skF_5', A_311)=k1_xboole_0 | k3_xboole_0(A_311, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_688])).
% 15.76/7.91  tff(c_162, plain, (![B_251, A_252]: (k3_xboole_0(k1_relat_1(B_251), A_252)=k1_relat_1(k7_relat_1(B_251, A_252)) | ~v1_relat_1(B_251))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.76/7.91  tff(c_169, plain, (![B_251]: (k1_relat_1(k7_relat_1(B_251, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_251))), inference(superposition, [status(thm), theory('equality')], [c_162, c_6])).
% 15.76/7.91  tff(c_781, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1('#skF_5') | k3_xboole_0(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_771, c_169])).
% 15.76/7.91  tff(c_787, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_105, c_781])).
% 15.76/7.91  tff(c_815, plain, (k3_xboole_0(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_787])).
% 15.76/7.91  tff(c_1054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1036, c_815])).
% 15.76/7.91  tff(c_1055, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_787])).
% 15.76/7.91  tff(c_1069, plain, (![B_13]: (k7_relat_1(k1_xboole_0, B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1055, c_14])).
% 15.76/7.91  tff(c_1186, plain, (![B_356]: (k7_relat_1(k1_xboole_0, B_356)=k1_xboole_0 | ~r1_xboole_0(B_356, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1069])).
% 15.76/7.91  tff(c_1194, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0 | k3_xboole_0(A_1, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1186])).
% 15.76/7.91  tff(c_1198, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1194])).
% 15.76/7.91  tff(c_1066, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1055, c_16])).
% 15.76/7.91  tff(c_1075, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1066])).
% 15.76/7.91  tff(c_1200, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_1075])).
% 15.76/7.91  tff(c_1201, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_1200])).
% 15.76/7.91  tff(c_732, plain, (![A_307]: (k7_relat_1('#skF_6', A_307)=k1_xboole_0 | k3_xboole_0(A_307, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_644])).
% 15.76/7.91  tff(c_742, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1('#skF_6') | k3_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_732, c_169])).
% 15.76/7.91  tff(c_748, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_104, c_742])).
% 15.76/7.91  tff(c_770, plain, (k3_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_748])).
% 15.76/7.91  tff(c_1218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1201, c_770])).
% 15.76/7.91  tff(c_1219, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_748])).
% 15.76/7.91  tff(c_1232, plain, (![B_13]: (k7_relat_1(k1_xboole_0, B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1219, c_14])).
% 15.76/7.91  tff(c_1297, plain, (![B_366]: (k7_relat_1(k1_xboole_0, B_366)=k1_xboole_0 | ~r1_xboole_0(B_366, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1232])).
% 15.76/7.91  tff(c_1305, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0 | k3_xboole_0(A_1, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1297])).
% 15.76/7.91  tff(c_1309, plain, (![A_1]: (k7_relat_1(k1_xboole_0, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1305])).
% 15.76/7.91  tff(c_1229, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1219, c_16])).
% 15.76/7.91  tff(c_1238, plain, (![A_14]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_14))=k3_xboole_0(k1_xboole_0, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1229])).
% 15.76/7.91  tff(c_1324, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1309, c_1238])).
% 15.76/7.91  tff(c_138, plain, (![A_243, B_244]: (k7_relat_1(A_243, B_244)=k1_xboole_0 | ~r1_xboole_0(B_244, k1_relat_1(A_243)) | ~v1_relat_1(A_243))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.76/7.91  tff(c_1462, plain, (![A_387, A_388]: (k7_relat_1(A_387, A_388)=k1_xboole_0 | ~v1_relat_1(A_387) | k3_xboole_0(A_388, k1_relat_1(A_387))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_138])).
% 15.76/7.91  tff(c_1498, plain, (![A_389]: (k7_relat_1(A_389, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_389))), inference(superposition, [status(thm), theory('equality')], [c_1324, c_1462])).
% 15.76/7.91  tff(c_1511, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_104, c_1498])).
% 15.76/7.91  tff(c_1510, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_105, c_1498])).
% 15.76/7.91  tff(c_1270, plain, (![A_365]: (k7_relat_1('#skF_6', A_365)=k1_xboole_0 | ~r1_subset_1(A_365, '#skF_4') | v1_xboole_0(A_365))), inference(negUnitSimplification, [status(thm)], [c_70, c_648])).
% 15.76/7.91  tff(c_1273, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1270])).
% 15.76/7.91  tff(c_1276, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_1273])).
% 15.76/7.91  tff(c_1283, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1276, c_630])).
% 15.76/7.91  tff(c_1290, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1283])).
% 15.76/7.91  tff(c_1342, plain, (![A_375]: (k7_relat_1('#skF_5', A_375)=k1_xboole_0 | k3_xboole_0(A_375, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_688])).
% 15.76/7.91  tff(c_520, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_5', A_14))=k3_xboole_0('#skF_3', A_14) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_512, c_16])).
% 15.76/7.91  tff(c_529, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_5', A_14))=k3_xboole_0('#skF_3', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_520])).
% 15.76/7.91  tff(c_1348, plain, (![A_375]: (k3_xboole_0('#skF_3', A_375)=k1_relat_1(k1_xboole_0) | k3_xboole_0(A_375, '#skF_3')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1342, c_529])).
% 15.76/7.91  tff(c_1361, plain, (![A_376]: (k3_xboole_0('#skF_3', A_376)=k1_xboole_0 | k3_xboole_0(A_376, '#skF_3')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1348])).
% 15.76/7.91  tff(c_1372, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1290, c_1361])).
% 15.76/7.91  tff(c_324, plain, (![A_276, B_277, C_278, D_279]: (k2_partfun1(A_276, B_277, C_278, D_279)=k7_relat_1(C_278, D_279) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))) | ~v1_funct_1(C_278))), inference(cnfTransformation, [status(thm)], [f_112])).
% 15.76/7.91  tff(c_328, plain, (![D_279]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_279)=k7_relat_1('#skF_5', D_279) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_324])).
% 15.76/7.91  tff(c_337, plain, (![D_279]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_279)=k7_relat_1('#skF_5', D_279))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_328])).
% 15.76/7.91  tff(c_326, plain, (![D_279]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_279)=k7_relat_1('#skF_6', D_279) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_324])).
% 15.76/7.91  tff(c_334, plain, (![D_279]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_279)=k7_relat_1('#skF_6', D_279))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_326])).
% 15.76/7.91  tff(c_238, plain, (![A_264, B_265, C_266]: (k9_subset_1(A_264, B_265, C_266)=k3_xboole_0(B_265, C_266) | ~m1_subset_1(C_266, k1_zfmisc_1(A_264)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.76/7.91  tff(c_253, plain, (![B_265]: (k9_subset_1('#skF_1', B_265, '#skF_4')=k3_xboole_0(B_265, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_238])).
% 15.76/7.91  tff(c_52, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_236])).
% 15.76/7.91  tff(c_107, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_52])).
% 15.76/7.91  tff(c_262, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_253, c_107])).
% 15.76/7.91  tff(c_1890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1511, c_1510, c_1372, c_1372, c_337, c_334, c_262])).
% 15.76/7.91  tff(c_1891, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_52])).
% 15.76/7.91  tff(c_1944, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_1891])).
% 15.76/7.91  tff(c_25318, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_25307, c_1944])).
% 15.76/7.91  tff(c_25332, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_3834, c_3833, c_3660, c_3660, c_2927, c_2927, c_5905, c_25318])).
% 15.76/7.91  tff(c_25334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_25332])).
% 15.76/7.91  tff(c_25335, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_1891])).
% 15.76/7.91  tff(c_47625, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_47616, c_25335])).
% 15.76/7.91  tff(c_47636, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_26974, c_26973, c_26738, c_26738, c_25438, c_25438, c_27168, c_47625])).
% 15.76/7.91  tff(c_47638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_47636])).
% 15.76/7.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.76/7.91  
% 15.76/7.91  Inference rules
% 15.76/7.91  ----------------------
% 15.76/7.91  #Ref     : 0
% 15.76/7.91  #Sup     : 10055
% 15.76/7.91  #Fact    : 0
% 15.76/7.91  #Define  : 0
% 15.76/7.91  #Split   : 50
% 15.76/7.91  #Chain   : 0
% 15.76/7.91  #Close   : 0
% 15.76/7.91  
% 15.76/7.91  Ordering : KBO
% 15.76/7.91  
% 15.76/7.91  Simplification rules
% 15.76/7.91  ----------------------
% 15.76/7.91  #Subsume      : 1112
% 15.76/7.91  #Demod        : 14334
% 15.76/7.91  #Tautology    : 6007
% 15.76/7.91  #SimpNegUnit  : 438
% 15.76/7.91  #BackRed      : 77
% 15.76/7.91  
% 15.76/7.91  #Partial instantiations: 0
% 15.76/7.91  #Strategies tried      : 1
% 15.76/7.91  
% 15.76/7.91  Timing (in seconds)
% 15.76/7.91  ----------------------
% 15.76/7.91  Preprocessing        : 0.44
% 15.76/7.91  Parsing              : 0.21
% 15.76/7.91  CNF conversion       : 0.06
% 15.76/7.91  Main loop            : 6.60
% 15.76/7.91  Inferencing          : 1.48
% 15.76/7.91  Reduction            : 2.68
% 15.76/7.91  Demodulation         : 2.13
% 15.76/7.91  BG Simplification    : 0.15
% 15.76/7.91  Subsumption          : 1.99
% 15.76/7.91  Abstraction          : 0.19
% 15.76/7.91  MUC search           : 0.00
% 15.76/7.91  Cooper               : 0.00
% 15.76/7.91  Total                : 7.17
% 15.76/7.91  Index Insertion      : 0.00
% 15.76/7.91  Index Deletion       : 0.00
% 15.76/7.91  Index Matching       : 0.00
% 15.76/7.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
