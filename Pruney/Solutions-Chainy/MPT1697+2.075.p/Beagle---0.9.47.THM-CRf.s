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
% DateTime   : Thu Dec  3 10:26:21 EST 2020

% Result     : Theorem 9.28s
% Output     : CNFRefutation 9.55s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 583 expanded)
%              Number of leaves         :   51 ( 231 expanded)
%              Depth                    :   12
%              Number of atoms          :  680 (3020 expanded)
%              Number of equality atoms :  114 ( 514 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_255,negated_conjecture,(
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

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_213,axiom,(
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

tff(f_131,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_179,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_82,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_78,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_28,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_64,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_1707,plain,(
    ! [B_472,A_473] :
      ( v1_relat_1(B_472)
      | ~ m1_subset_1(B_472,k1_zfmisc_1(A_473))
      | ~ v1_relat_1(A_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1713,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_1707])).

tff(c_1725,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1713])).

tff(c_1728,plain,(
    ! [A_474,B_475] :
      ( r2_hidden('#skF_2'(A_474,B_475),A_474)
      | r1_xboole_0(A_474,B_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1732,plain,(
    ! [A_474,B_475] :
      ( ~ v1_xboole_0(A_474)
      | r1_xboole_0(A_474,B_475) ) ),
    inference(resolution,[status(thm)],[c_1728,c_2])).

tff(c_1858,plain,(
    ! [A_504,B_505] :
      ( k7_relat_1(A_504,B_505) = k1_xboole_0
      | ~ r1_xboole_0(B_505,k1_relat_1(A_504))
      | ~ v1_relat_1(A_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1884,plain,(
    ! [A_506,A_507] :
      ( k7_relat_1(A_506,A_507) = k1_xboole_0
      | ~ v1_relat_1(A_506)
      | ~ v1_xboole_0(A_507) ) ),
    inference(resolution,[status(thm)],[c_1732,c_1858])).

tff(c_1894,plain,(
    ! [A_508] :
      ( k7_relat_1('#skF_8',A_508) = k1_xboole_0
      | ~ v1_xboole_0(A_508) ) ),
    inference(resolution,[status(thm)],[c_1725,c_1884])).

tff(c_1898,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1894])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_1710,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_70,c_1707])).

tff(c_1722,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1710])).

tff(c_1924,plain,(
    ! [A_511] :
      ( k7_relat_1('#skF_7',A_511) = k1_xboole_0
      | ~ v1_xboole_0(A_511) ) ),
    inference(resolution,[status(thm)],[c_1722,c_1884])).

tff(c_1928,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1924])).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_76,plain,(
    r1_subset_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_1846,plain,(
    ! [A_501,B_502] :
      ( r1_xboole_0(A_501,B_502)
      | ~ r1_subset_1(A_501,B_502)
      | v1_xboole_0(B_502)
      | v1_xboole_0(A_501) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6587,plain,(
    ! [A_1105,B_1106] :
      ( k3_xboole_0(A_1105,B_1106) = k1_xboole_0
      | ~ r1_subset_1(A_1105,B_1106)
      | v1_xboole_0(B_1106)
      | v1_xboole_0(A_1105) ) ),
    inference(resolution,[status(thm)],[c_1846,c_6])).

tff(c_6596,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_6587])).

tff(c_6603,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_80,c_6596])).

tff(c_5263,plain,(
    ! [A_986,B_987,C_988] :
      ( k9_subset_1(A_986,B_987,C_988) = k3_xboole_0(B_987,C_988)
      | ~ m1_subset_1(C_988,k1_zfmisc_1(A_986)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5275,plain,(
    ! [B_987] : k9_subset_1('#skF_3',B_987,'#skF_6') = k3_xboole_0(B_987,'#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_5263])).

tff(c_74,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_72,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_68,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_66,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_6714,plain,(
    ! [C_1124,A_1122,F_1123,E_1120,D_1121,B_1119] :
      ( v1_funct_1(k1_tmap_1(A_1122,B_1119,C_1124,D_1121,E_1120,F_1123))
      | ~ m1_subset_1(F_1123,k1_zfmisc_1(k2_zfmisc_1(D_1121,B_1119)))
      | ~ v1_funct_2(F_1123,D_1121,B_1119)
      | ~ v1_funct_1(F_1123)
      | ~ m1_subset_1(E_1120,k1_zfmisc_1(k2_zfmisc_1(C_1124,B_1119)))
      | ~ v1_funct_2(E_1120,C_1124,B_1119)
      | ~ v1_funct_1(E_1120)
      | ~ m1_subset_1(D_1121,k1_zfmisc_1(A_1122))
      | v1_xboole_0(D_1121)
      | ~ m1_subset_1(C_1124,k1_zfmisc_1(A_1122))
      | v1_xboole_0(C_1124)
      | v1_xboole_0(B_1119)
      | v1_xboole_0(A_1122) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_6718,plain,(
    ! [A_1122,C_1124,E_1120] :
      ( v1_funct_1(k1_tmap_1(A_1122,'#skF_4',C_1124,'#skF_6',E_1120,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_1120,k1_zfmisc_1(k2_zfmisc_1(C_1124,'#skF_4')))
      | ~ v1_funct_2(E_1120,C_1124,'#skF_4')
      | ~ v1_funct_1(E_1120)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1122))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1124,k1_zfmisc_1(A_1122))
      | v1_xboole_0(C_1124)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1122) ) ),
    inference(resolution,[status(thm)],[c_64,c_6714])).

tff(c_6725,plain,(
    ! [A_1122,C_1124,E_1120] :
      ( v1_funct_1(k1_tmap_1(A_1122,'#skF_4',C_1124,'#skF_6',E_1120,'#skF_8'))
      | ~ m1_subset_1(E_1120,k1_zfmisc_1(k2_zfmisc_1(C_1124,'#skF_4')))
      | ~ v1_funct_2(E_1120,C_1124,'#skF_4')
      | ~ v1_funct_1(E_1120)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1122))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1124,k1_zfmisc_1(A_1122))
      | v1_xboole_0(C_1124)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_6718])).

tff(c_6771,plain,(
    ! [A_1128,C_1129,E_1130] :
      ( v1_funct_1(k1_tmap_1(A_1128,'#skF_4',C_1129,'#skF_6',E_1130,'#skF_8'))
      | ~ m1_subset_1(E_1130,k1_zfmisc_1(k2_zfmisc_1(C_1129,'#skF_4')))
      | ~ v1_funct_2(E_1130,C_1129,'#skF_4')
      | ~ v1_funct_1(E_1130)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1128))
      | ~ m1_subset_1(C_1129,k1_zfmisc_1(A_1128))
      | v1_xboole_0(C_1129)
      | v1_xboole_0(A_1128) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80,c_6725])).

tff(c_6773,plain,(
    ! [A_1128] :
      ( v1_funct_1(k1_tmap_1(A_1128,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1128))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1128))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1128) ) ),
    inference(resolution,[status(thm)],[c_70,c_6771])).

tff(c_6778,plain,(
    ! [A_1128] :
      ( v1_funct_1(k1_tmap_1(A_1128,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1128))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1128))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_6773])).

tff(c_6973,plain,(
    ! [A_1174] :
      ( v1_funct_1(k1_tmap_1(A_1174,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1174))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1174))
      | v1_xboole_0(A_1174) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_6778])).

tff(c_6976,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_6973])).

tff(c_6979,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_6976])).

tff(c_6980,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_6979])).

tff(c_6509,plain,(
    ! [A_1095,B_1096,C_1097,D_1098] :
      ( k2_partfun1(A_1095,B_1096,C_1097,D_1098) = k7_relat_1(C_1097,D_1098)
      | ~ m1_subset_1(C_1097,k1_zfmisc_1(k2_zfmisc_1(A_1095,B_1096)))
      | ~ v1_funct_1(C_1097) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_6511,plain,(
    ! [D_1098] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_1098) = k7_relat_1('#skF_7',D_1098)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_6509])).

tff(c_6516,plain,(
    ! [D_1098] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_1098) = k7_relat_1('#skF_7',D_1098) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6511])).

tff(c_6513,plain,(
    ! [D_1098] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_1098) = k7_relat_1('#skF_8',D_1098)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_64,c_6509])).

tff(c_6519,plain,(
    ! [D_1098] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_1098) = k7_relat_1('#skF_8',D_1098) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6513])).

tff(c_58,plain,(
    ! [F_177,D_175,A_172,C_174,E_176,B_173] :
      ( v1_funct_2(k1_tmap_1(A_172,B_173,C_174,D_175,E_176,F_177),k4_subset_1(A_172,C_174,D_175),B_173)
      | ~ m1_subset_1(F_177,k1_zfmisc_1(k2_zfmisc_1(D_175,B_173)))
      | ~ v1_funct_2(F_177,D_175,B_173)
      | ~ v1_funct_1(F_177)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(C_174,B_173)))
      | ~ v1_funct_2(E_176,C_174,B_173)
      | ~ v1_funct_1(E_176)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(A_172))
      | v1_xboole_0(D_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(A_172))
      | v1_xboole_0(C_174)
      | v1_xboole_0(B_173)
      | v1_xboole_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_56,plain,(
    ! [F_177,D_175,A_172,C_174,E_176,B_173] :
      ( m1_subset_1(k1_tmap_1(A_172,B_173,C_174,D_175,E_176,F_177),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_172,C_174,D_175),B_173)))
      | ~ m1_subset_1(F_177,k1_zfmisc_1(k2_zfmisc_1(D_175,B_173)))
      | ~ v1_funct_2(F_177,D_175,B_173)
      | ~ v1_funct_1(F_177)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(C_174,B_173)))
      | ~ v1_funct_2(E_176,C_174,B_173)
      | ~ v1_funct_1(E_176)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(A_172))
      | v1_xboole_0(D_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(A_172))
      | v1_xboole_0(C_174)
      | v1_xboole_0(B_173)
      | v1_xboole_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_7136,plain,(
    ! [E_1213,C_1214,A_1212,B_1215,D_1211,F_1216] :
      ( k2_partfun1(k4_subset_1(A_1212,C_1214,D_1211),B_1215,k1_tmap_1(A_1212,B_1215,C_1214,D_1211,E_1213,F_1216),C_1214) = E_1213
      | ~ m1_subset_1(k1_tmap_1(A_1212,B_1215,C_1214,D_1211,E_1213,F_1216),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1212,C_1214,D_1211),B_1215)))
      | ~ v1_funct_2(k1_tmap_1(A_1212,B_1215,C_1214,D_1211,E_1213,F_1216),k4_subset_1(A_1212,C_1214,D_1211),B_1215)
      | ~ v1_funct_1(k1_tmap_1(A_1212,B_1215,C_1214,D_1211,E_1213,F_1216))
      | k2_partfun1(D_1211,B_1215,F_1216,k9_subset_1(A_1212,C_1214,D_1211)) != k2_partfun1(C_1214,B_1215,E_1213,k9_subset_1(A_1212,C_1214,D_1211))
      | ~ m1_subset_1(F_1216,k1_zfmisc_1(k2_zfmisc_1(D_1211,B_1215)))
      | ~ v1_funct_2(F_1216,D_1211,B_1215)
      | ~ v1_funct_1(F_1216)
      | ~ m1_subset_1(E_1213,k1_zfmisc_1(k2_zfmisc_1(C_1214,B_1215)))
      | ~ v1_funct_2(E_1213,C_1214,B_1215)
      | ~ v1_funct_1(E_1213)
      | ~ m1_subset_1(D_1211,k1_zfmisc_1(A_1212))
      | v1_xboole_0(D_1211)
      | ~ m1_subset_1(C_1214,k1_zfmisc_1(A_1212))
      | v1_xboole_0(C_1214)
      | v1_xboole_0(B_1215)
      | v1_xboole_0(A_1212) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_7543,plain,(
    ! [D_1299,A_1300,E_1298,F_1301,C_1302,B_1297] :
      ( k2_partfun1(k4_subset_1(A_1300,C_1302,D_1299),B_1297,k1_tmap_1(A_1300,B_1297,C_1302,D_1299,E_1298,F_1301),C_1302) = E_1298
      | ~ v1_funct_2(k1_tmap_1(A_1300,B_1297,C_1302,D_1299,E_1298,F_1301),k4_subset_1(A_1300,C_1302,D_1299),B_1297)
      | ~ v1_funct_1(k1_tmap_1(A_1300,B_1297,C_1302,D_1299,E_1298,F_1301))
      | k2_partfun1(D_1299,B_1297,F_1301,k9_subset_1(A_1300,C_1302,D_1299)) != k2_partfun1(C_1302,B_1297,E_1298,k9_subset_1(A_1300,C_1302,D_1299))
      | ~ m1_subset_1(F_1301,k1_zfmisc_1(k2_zfmisc_1(D_1299,B_1297)))
      | ~ v1_funct_2(F_1301,D_1299,B_1297)
      | ~ v1_funct_1(F_1301)
      | ~ m1_subset_1(E_1298,k1_zfmisc_1(k2_zfmisc_1(C_1302,B_1297)))
      | ~ v1_funct_2(E_1298,C_1302,B_1297)
      | ~ v1_funct_1(E_1298)
      | ~ m1_subset_1(D_1299,k1_zfmisc_1(A_1300))
      | v1_xboole_0(D_1299)
      | ~ m1_subset_1(C_1302,k1_zfmisc_1(A_1300))
      | v1_xboole_0(C_1302)
      | v1_xboole_0(B_1297)
      | v1_xboole_0(A_1300) ) ),
    inference(resolution,[status(thm)],[c_56,c_7136])).

tff(c_8152,plain,(
    ! [D_1369,B_1367,F_1371,C_1372,A_1370,E_1368] :
      ( k2_partfun1(k4_subset_1(A_1370,C_1372,D_1369),B_1367,k1_tmap_1(A_1370,B_1367,C_1372,D_1369,E_1368,F_1371),C_1372) = E_1368
      | ~ v1_funct_1(k1_tmap_1(A_1370,B_1367,C_1372,D_1369,E_1368,F_1371))
      | k2_partfun1(D_1369,B_1367,F_1371,k9_subset_1(A_1370,C_1372,D_1369)) != k2_partfun1(C_1372,B_1367,E_1368,k9_subset_1(A_1370,C_1372,D_1369))
      | ~ m1_subset_1(F_1371,k1_zfmisc_1(k2_zfmisc_1(D_1369,B_1367)))
      | ~ v1_funct_2(F_1371,D_1369,B_1367)
      | ~ v1_funct_1(F_1371)
      | ~ m1_subset_1(E_1368,k1_zfmisc_1(k2_zfmisc_1(C_1372,B_1367)))
      | ~ v1_funct_2(E_1368,C_1372,B_1367)
      | ~ v1_funct_1(E_1368)
      | ~ m1_subset_1(D_1369,k1_zfmisc_1(A_1370))
      | v1_xboole_0(D_1369)
      | ~ m1_subset_1(C_1372,k1_zfmisc_1(A_1370))
      | v1_xboole_0(C_1372)
      | v1_xboole_0(B_1367)
      | v1_xboole_0(A_1370) ) ),
    inference(resolution,[status(thm)],[c_58,c_7543])).

tff(c_8158,plain,(
    ! [A_1370,C_1372,E_1368] :
      ( k2_partfun1(k4_subset_1(A_1370,C_1372,'#skF_6'),'#skF_4',k1_tmap_1(A_1370,'#skF_4',C_1372,'#skF_6',E_1368,'#skF_8'),C_1372) = E_1368
      | ~ v1_funct_1(k1_tmap_1(A_1370,'#skF_4',C_1372,'#skF_6',E_1368,'#skF_8'))
      | k2_partfun1(C_1372,'#skF_4',E_1368,k9_subset_1(A_1370,C_1372,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_1370,C_1372,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_1368,k1_zfmisc_1(k2_zfmisc_1(C_1372,'#skF_4')))
      | ~ v1_funct_2(E_1368,C_1372,'#skF_4')
      | ~ v1_funct_1(E_1368)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1370))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1372,k1_zfmisc_1(A_1370))
      | v1_xboole_0(C_1372)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1370) ) ),
    inference(resolution,[status(thm)],[c_64,c_8152])).

tff(c_8166,plain,(
    ! [A_1370,C_1372,E_1368] :
      ( k2_partfun1(k4_subset_1(A_1370,C_1372,'#skF_6'),'#skF_4',k1_tmap_1(A_1370,'#skF_4',C_1372,'#skF_6',E_1368,'#skF_8'),C_1372) = E_1368
      | ~ v1_funct_1(k1_tmap_1(A_1370,'#skF_4',C_1372,'#skF_6',E_1368,'#skF_8'))
      | k2_partfun1(C_1372,'#skF_4',E_1368,k9_subset_1(A_1370,C_1372,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1370,C_1372,'#skF_6'))
      | ~ m1_subset_1(E_1368,k1_zfmisc_1(k2_zfmisc_1(C_1372,'#skF_4')))
      | ~ v1_funct_2(E_1368,C_1372,'#skF_4')
      | ~ v1_funct_1(E_1368)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1370))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1372,k1_zfmisc_1(A_1370))
      | v1_xboole_0(C_1372)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1370) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_6519,c_8158])).

tff(c_8569,plain,(
    ! [A_1421,C_1422,E_1423] :
      ( k2_partfun1(k4_subset_1(A_1421,C_1422,'#skF_6'),'#skF_4',k1_tmap_1(A_1421,'#skF_4',C_1422,'#skF_6',E_1423,'#skF_8'),C_1422) = E_1423
      | ~ v1_funct_1(k1_tmap_1(A_1421,'#skF_4',C_1422,'#skF_6',E_1423,'#skF_8'))
      | k2_partfun1(C_1422,'#skF_4',E_1423,k9_subset_1(A_1421,C_1422,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1421,C_1422,'#skF_6'))
      | ~ m1_subset_1(E_1423,k1_zfmisc_1(k2_zfmisc_1(C_1422,'#skF_4')))
      | ~ v1_funct_2(E_1423,C_1422,'#skF_4')
      | ~ v1_funct_1(E_1423)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1421))
      | ~ m1_subset_1(C_1422,k1_zfmisc_1(A_1421))
      | v1_xboole_0(C_1422)
      | v1_xboole_0(A_1421) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80,c_8166])).

tff(c_8574,plain,(
    ! [A_1421] :
      ( k2_partfun1(k4_subset_1(A_1421,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1421,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1421,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_1421,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1421,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1421))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1421))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1421) ) ),
    inference(resolution,[status(thm)],[c_70,c_8569])).

tff(c_8582,plain,(
    ! [A_1421] :
      ( k2_partfun1(k4_subset_1(A_1421,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1421,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1421,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1421,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1421,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1421))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1421))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1421) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_6516,c_8574])).

tff(c_8606,plain,(
    ! [A_1424] :
      ( k2_partfun1(k4_subset_1(A_1424,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1424,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1424,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1424,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1424,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1424))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1424))
      | v1_xboole_0(A_1424) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_8582])).

tff(c_3128,plain,(
    ! [A_632,B_633] :
      ( k3_xboole_0(A_632,B_633) = k1_xboole_0
      | ~ r1_subset_1(A_632,B_633)
      | v1_xboole_0(B_633)
      | v1_xboole_0(A_632) ) ),
    inference(resolution,[status(thm)],[c_1846,c_6])).

tff(c_3134,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_3128])).

tff(c_3140,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_80,c_3134])).

tff(c_1984,plain,(
    ! [A_525,B_526,C_527] :
      ( k9_subset_1(A_525,B_526,C_527) = k3_xboole_0(B_526,C_527)
      | ~ m1_subset_1(C_527,k1_zfmisc_1(A_525)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1996,plain,(
    ! [B_526] : k9_subset_1('#skF_3',B_526,'#skF_6') = k3_xboole_0(B_526,'#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_1984])).

tff(c_3257,plain,(
    ! [D_645,F_647,E_644,C_648,B_643,A_646] :
      ( v1_funct_1(k1_tmap_1(A_646,B_643,C_648,D_645,E_644,F_647))
      | ~ m1_subset_1(F_647,k1_zfmisc_1(k2_zfmisc_1(D_645,B_643)))
      | ~ v1_funct_2(F_647,D_645,B_643)
      | ~ v1_funct_1(F_647)
      | ~ m1_subset_1(E_644,k1_zfmisc_1(k2_zfmisc_1(C_648,B_643)))
      | ~ v1_funct_2(E_644,C_648,B_643)
      | ~ v1_funct_1(E_644)
      | ~ m1_subset_1(D_645,k1_zfmisc_1(A_646))
      | v1_xboole_0(D_645)
      | ~ m1_subset_1(C_648,k1_zfmisc_1(A_646))
      | v1_xboole_0(C_648)
      | v1_xboole_0(B_643)
      | v1_xboole_0(A_646) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_3261,plain,(
    ! [A_646,C_648,E_644] :
      ( v1_funct_1(k1_tmap_1(A_646,'#skF_4',C_648,'#skF_6',E_644,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_644,k1_zfmisc_1(k2_zfmisc_1(C_648,'#skF_4')))
      | ~ v1_funct_2(E_644,C_648,'#skF_4')
      | ~ v1_funct_1(E_644)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_646))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_648,k1_zfmisc_1(A_646))
      | v1_xboole_0(C_648)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_646) ) ),
    inference(resolution,[status(thm)],[c_64,c_3257])).

tff(c_3268,plain,(
    ! [A_646,C_648,E_644] :
      ( v1_funct_1(k1_tmap_1(A_646,'#skF_4',C_648,'#skF_6',E_644,'#skF_8'))
      | ~ m1_subset_1(E_644,k1_zfmisc_1(k2_zfmisc_1(C_648,'#skF_4')))
      | ~ v1_funct_2(E_644,C_648,'#skF_4')
      | ~ v1_funct_1(E_644)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_646))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_648,k1_zfmisc_1(A_646))
      | v1_xboole_0(C_648)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_646) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_3261])).

tff(c_3322,plain,(
    ! [A_653,C_654,E_655] :
      ( v1_funct_1(k1_tmap_1(A_653,'#skF_4',C_654,'#skF_6',E_655,'#skF_8'))
      | ~ m1_subset_1(E_655,k1_zfmisc_1(k2_zfmisc_1(C_654,'#skF_4')))
      | ~ v1_funct_2(E_655,C_654,'#skF_4')
      | ~ v1_funct_1(E_655)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_653))
      | ~ m1_subset_1(C_654,k1_zfmisc_1(A_653))
      | v1_xboole_0(C_654)
      | v1_xboole_0(A_653) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80,c_3268])).

tff(c_3324,plain,(
    ! [A_653] :
      ( v1_funct_1(k1_tmap_1(A_653,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_653))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_653))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_653) ) ),
    inference(resolution,[status(thm)],[c_70,c_3322])).

tff(c_3329,plain,(
    ! [A_653] :
      ( v1_funct_1(k1_tmap_1(A_653,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_653))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_653))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_653) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3324])).

tff(c_3537,plain,(
    ! [A_694] :
      ( v1_funct_1(k1_tmap_1(A_694,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_694))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_694))
      | v1_xboole_0(A_694) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_3329])).

tff(c_3540,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_3537])).

tff(c_3543,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3540])).

tff(c_3544,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3543])).

tff(c_2986,plain,(
    ! [A_618,B_619,C_620,D_621] :
      ( k2_partfun1(A_618,B_619,C_620,D_621) = k7_relat_1(C_620,D_621)
      | ~ m1_subset_1(C_620,k1_zfmisc_1(k2_zfmisc_1(A_618,B_619)))
      | ~ v1_funct_1(C_620) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2988,plain,(
    ! [D_621] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_621) = k7_relat_1('#skF_7',D_621)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_2986])).

tff(c_2993,plain,(
    ! [D_621] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_621) = k7_relat_1('#skF_7',D_621) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2988])).

tff(c_2990,plain,(
    ! [D_621] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_621) = k7_relat_1('#skF_8',D_621)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_64,c_2986])).

tff(c_2996,plain,(
    ! [D_621] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_621) = k7_relat_1('#skF_8',D_621) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2990])).

tff(c_3581,plain,(
    ! [A_705,E_706,F_709,C_707,D_704,B_708] :
      ( k2_partfun1(k4_subset_1(A_705,C_707,D_704),B_708,k1_tmap_1(A_705,B_708,C_707,D_704,E_706,F_709),D_704) = F_709
      | ~ m1_subset_1(k1_tmap_1(A_705,B_708,C_707,D_704,E_706,F_709),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_705,C_707,D_704),B_708)))
      | ~ v1_funct_2(k1_tmap_1(A_705,B_708,C_707,D_704,E_706,F_709),k4_subset_1(A_705,C_707,D_704),B_708)
      | ~ v1_funct_1(k1_tmap_1(A_705,B_708,C_707,D_704,E_706,F_709))
      | k2_partfun1(D_704,B_708,F_709,k9_subset_1(A_705,C_707,D_704)) != k2_partfun1(C_707,B_708,E_706,k9_subset_1(A_705,C_707,D_704))
      | ~ m1_subset_1(F_709,k1_zfmisc_1(k2_zfmisc_1(D_704,B_708)))
      | ~ v1_funct_2(F_709,D_704,B_708)
      | ~ v1_funct_1(F_709)
      | ~ m1_subset_1(E_706,k1_zfmisc_1(k2_zfmisc_1(C_707,B_708)))
      | ~ v1_funct_2(E_706,C_707,B_708)
      | ~ v1_funct_1(E_706)
      | ~ m1_subset_1(D_704,k1_zfmisc_1(A_705))
      | v1_xboole_0(D_704)
      | ~ m1_subset_1(C_707,k1_zfmisc_1(A_705))
      | v1_xboole_0(C_707)
      | v1_xboole_0(B_708)
      | v1_xboole_0(A_705) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_4229,plain,(
    ! [B_858,A_861,C_863,E_859,F_862,D_860] :
      ( k2_partfun1(k4_subset_1(A_861,C_863,D_860),B_858,k1_tmap_1(A_861,B_858,C_863,D_860,E_859,F_862),D_860) = F_862
      | ~ v1_funct_2(k1_tmap_1(A_861,B_858,C_863,D_860,E_859,F_862),k4_subset_1(A_861,C_863,D_860),B_858)
      | ~ v1_funct_1(k1_tmap_1(A_861,B_858,C_863,D_860,E_859,F_862))
      | k2_partfun1(D_860,B_858,F_862,k9_subset_1(A_861,C_863,D_860)) != k2_partfun1(C_863,B_858,E_859,k9_subset_1(A_861,C_863,D_860))
      | ~ m1_subset_1(F_862,k1_zfmisc_1(k2_zfmisc_1(D_860,B_858)))
      | ~ v1_funct_2(F_862,D_860,B_858)
      | ~ v1_funct_1(F_862)
      | ~ m1_subset_1(E_859,k1_zfmisc_1(k2_zfmisc_1(C_863,B_858)))
      | ~ v1_funct_2(E_859,C_863,B_858)
      | ~ v1_funct_1(E_859)
      | ~ m1_subset_1(D_860,k1_zfmisc_1(A_861))
      | v1_xboole_0(D_860)
      | ~ m1_subset_1(C_863,k1_zfmisc_1(A_861))
      | v1_xboole_0(C_863)
      | v1_xboole_0(B_858)
      | v1_xboole_0(A_861) ) ),
    inference(resolution,[status(thm)],[c_56,c_3581])).

tff(c_4818,plain,(
    ! [C_923,A_921,E_919,B_918,D_920,F_922] :
      ( k2_partfun1(k4_subset_1(A_921,C_923,D_920),B_918,k1_tmap_1(A_921,B_918,C_923,D_920,E_919,F_922),D_920) = F_922
      | ~ v1_funct_1(k1_tmap_1(A_921,B_918,C_923,D_920,E_919,F_922))
      | k2_partfun1(D_920,B_918,F_922,k9_subset_1(A_921,C_923,D_920)) != k2_partfun1(C_923,B_918,E_919,k9_subset_1(A_921,C_923,D_920))
      | ~ m1_subset_1(F_922,k1_zfmisc_1(k2_zfmisc_1(D_920,B_918)))
      | ~ v1_funct_2(F_922,D_920,B_918)
      | ~ v1_funct_1(F_922)
      | ~ m1_subset_1(E_919,k1_zfmisc_1(k2_zfmisc_1(C_923,B_918)))
      | ~ v1_funct_2(E_919,C_923,B_918)
      | ~ v1_funct_1(E_919)
      | ~ m1_subset_1(D_920,k1_zfmisc_1(A_921))
      | v1_xboole_0(D_920)
      | ~ m1_subset_1(C_923,k1_zfmisc_1(A_921))
      | v1_xboole_0(C_923)
      | v1_xboole_0(B_918)
      | v1_xboole_0(A_921) ) ),
    inference(resolution,[status(thm)],[c_58,c_4229])).

tff(c_4824,plain,(
    ! [A_921,C_923,E_919] :
      ( k2_partfun1(k4_subset_1(A_921,C_923,'#skF_6'),'#skF_4',k1_tmap_1(A_921,'#skF_4',C_923,'#skF_6',E_919,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_921,'#skF_4',C_923,'#skF_6',E_919,'#skF_8'))
      | k2_partfun1(C_923,'#skF_4',E_919,k9_subset_1(A_921,C_923,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_921,C_923,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_919,k1_zfmisc_1(k2_zfmisc_1(C_923,'#skF_4')))
      | ~ v1_funct_2(E_919,C_923,'#skF_4')
      | ~ v1_funct_1(E_919)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_921))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_923,k1_zfmisc_1(A_921))
      | v1_xboole_0(C_923)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_921) ) ),
    inference(resolution,[status(thm)],[c_64,c_4818])).

tff(c_4832,plain,(
    ! [A_921,C_923,E_919] :
      ( k2_partfun1(k4_subset_1(A_921,C_923,'#skF_6'),'#skF_4',k1_tmap_1(A_921,'#skF_4',C_923,'#skF_6',E_919,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_921,'#skF_4',C_923,'#skF_6',E_919,'#skF_8'))
      | k2_partfun1(C_923,'#skF_4',E_919,k9_subset_1(A_921,C_923,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_921,C_923,'#skF_6'))
      | ~ m1_subset_1(E_919,k1_zfmisc_1(k2_zfmisc_1(C_923,'#skF_4')))
      | ~ v1_funct_2(E_919,C_923,'#skF_4')
      | ~ v1_funct_1(E_919)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_921))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_923,k1_zfmisc_1(A_921))
      | v1_xboole_0(C_923)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_921) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2996,c_4824])).

tff(c_5129,plain,(
    ! [A_968,C_969,E_970] :
      ( k2_partfun1(k4_subset_1(A_968,C_969,'#skF_6'),'#skF_4',k1_tmap_1(A_968,'#skF_4',C_969,'#skF_6',E_970,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_968,'#skF_4',C_969,'#skF_6',E_970,'#skF_8'))
      | k2_partfun1(C_969,'#skF_4',E_970,k9_subset_1(A_968,C_969,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_968,C_969,'#skF_6'))
      | ~ m1_subset_1(E_970,k1_zfmisc_1(k2_zfmisc_1(C_969,'#skF_4')))
      | ~ v1_funct_2(E_970,C_969,'#skF_4')
      | ~ v1_funct_1(E_970)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_968))
      | ~ m1_subset_1(C_969,k1_zfmisc_1(A_968))
      | v1_xboole_0(C_969)
      | v1_xboole_0(A_968) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80,c_4832])).

tff(c_5134,plain,(
    ! [A_968] :
      ( k2_partfun1(k4_subset_1(A_968,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_968,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_968,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_968,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_968,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_968))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_968))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_968) ) ),
    inference(resolution,[status(thm)],[c_70,c_5129])).

tff(c_5142,plain,(
    ! [A_968] :
      ( k2_partfun1(k4_subset_1(A_968,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_968,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_968,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_968,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_968,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_968))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_968))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_968) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2993,c_5134])).

tff(c_5183,plain,(
    ! [A_972] :
      ( k2_partfun1(k4_subset_1(A_972,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_972,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_972,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_972,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_972,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_972))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_972))
      | v1_xboole_0(A_972) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_5142])).

tff(c_124,plain,(
    ! [A_250,B_251] :
      ( r2_hidden('#skF_2'(A_250,B_251),B_251)
      | r1_xboole_0(A_250,B_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_129,plain,(
    ! [B_252,A_253] :
      ( ~ v1_xboole_0(B_252)
      | r1_xboole_0(A_253,B_252) ) ),
    inference(resolution,[status(thm)],[c_124,c_2])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_136,plain,(
    ! [B_252,A_253] :
      ( r1_xboole_0(B_252,A_253)
      | ~ v1_xboole_0(B_252) ) ),
    inference(resolution,[status(thm)],[c_129,c_12])).

tff(c_201,plain,(
    ! [B_266,A_267] :
      ( v1_relat_1(B_266)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(A_267))
      | ~ v1_relat_1(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_204,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_70,c_201])).

tff(c_216,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_204])).

tff(c_232,plain,(
    ! [C_270,A_271,B_272] :
      ( v4_relat_1(C_270,A_271)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_239,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_232])).

tff(c_322,plain,(
    ! [B_286,A_287] :
      ( k1_relat_1(B_286) = A_287
      | ~ v1_partfun1(B_286,A_287)
      | ~ v4_relat_1(B_286,A_287)
      | ~ v1_relat_1(B_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_328,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_239,c_322])).

tff(c_334,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_328])).

tff(c_893,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_334])).

tff(c_1168,plain,(
    ! [C_405,A_406,B_407] :
      ( v1_partfun1(C_405,A_406)
      | ~ v1_funct_2(C_405,A_406,B_407)
      | ~ v1_funct_1(C_405)
      | ~ m1_subset_1(C_405,k1_zfmisc_1(k2_zfmisc_1(A_406,B_407)))
      | v1_xboole_0(B_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1171,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_1168])).

tff(c_1177,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1171])).

tff(c_1179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_893,c_1177])).

tff(c_1180,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_334])).

tff(c_30,plain,(
    ! [A_27,B_29] :
      ( k7_relat_1(A_27,B_29) = k1_xboole_0
      | ~ r1_xboole_0(B_29,k1_relat_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1185,plain,(
    ! [B_29] :
      ( k7_relat_1('#skF_7',B_29) = k1_xboole_0
      | ~ r1_xboole_0(B_29,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1180,c_30])).

tff(c_1234,plain,(
    ! [B_410] :
      ( k7_relat_1('#skF_7',B_410) = k1_xboole_0
      | ~ r1_xboole_0(B_410,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_1185])).

tff(c_1262,plain,(
    ! [B_411] :
      ( k7_relat_1('#skF_7',B_411) = k1_xboole_0
      | ~ v1_xboole_0(B_411) ) ),
    inference(resolution,[status(thm)],[c_136,c_1234])).

tff(c_1266,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1262])).

tff(c_207,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_201])).

tff(c_219,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_207])).

tff(c_240,plain,(
    v4_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_232])).

tff(c_325,plain,
    ( k1_relat_1('#skF_8') = '#skF_6'
    | ~ v1_partfun1('#skF_8','#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_240,c_322])).

tff(c_331,plain,
    ( k1_relat_1('#skF_8') = '#skF_6'
    | ~ v1_partfun1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_325])).

tff(c_335,plain,(
    ~ v1_partfun1('#skF_8','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_860,plain,(
    ! [C_367,A_368,B_369] :
      ( v1_partfun1(C_367,A_368)
      | ~ v1_funct_2(C_367,A_368,B_369)
      | ~ v1_funct_1(C_367)
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1(A_368,B_369)))
      | v1_xboole_0(B_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_866,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
    | ~ v1_funct_1('#skF_8')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_860])).

tff(c_873,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_866])).

tff(c_875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_335,c_873])).

tff(c_876,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_881,plain,(
    ! [B_29] :
      ( k7_relat_1('#skF_8',B_29) = k1_xboole_0
      | ~ r1_xboole_0(B_29,'#skF_6')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_876,c_30])).

tff(c_1197,plain,(
    ! [B_408] :
      ( k7_relat_1('#skF_8',B_408) = k1_xboole_0
      | ~ r1_xboole_0(B_408,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_881])).

tff(c_1225,plain,(
    ! [B_409] :
      ( k7_relat_1('#skF_8',B_409) = k1_xboole_0
      | ~ v1_xboole_0(B_409) ) ),
    inference(resolution,[status(thm)],[c_136,c_1197])).

tff(c_1229,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1225])).

tff(c_281,plain,(
    ! [A_282,B_283] :
      ( r1_xboole_0(A_282,B_283)
      | ~ r1_subset_1(A_282,B_283)
      | v1_xboole_0(B_283)
      | v1_xboole_0(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1667,plain,(
    ! [A_464,B_465] :
      ( k3_xboole_0(A_464,B_465) = k1_xboole_0
      | ~ r1_subset_1(A_464,B_465)
      | v1_xboole_0(B_465)
      | v1_xboole_0(A_464) ) ),
    inference(resolution,[status(thm)],[c_281,c_6])).

tff(c_1673,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_1667])).

tff(c_1679,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_80,c_1673])).

tff(c_1431,plain,(
    ! [A_427,B_428,C_429,D_430] :
      ( k2_partfun1(A_427,B_428,C_429,D_430) = k7_relat_1(C_429,D_430)
      | ~ m1_subset_1(C_429,k1_zfmisc_1(k2_zfmisc_1(A_427,B_428)))
      | ~ v1_funct_1(C_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1435,plain,(
    ! [D_430] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_430) = k7_relat_1('#skF_8',D_430)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_64,c_1431])).

tff(c_1441,plain,(
    ! [D_430] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_430) = k7_relat_1('#skF_8',D_430) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1435])).

tff(c_1433,plain,(
    ! [D_430] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_430) = k7_relat_1('#skF_7',D_430)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_1431])).

tff(c_1438,plain,(
    ! [D_430] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_430) = k7_relat_1('#skF_7',D_430) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1433])).

tff(c_1271,plain,(
    ! [A_412,B_413,C_414] :
      ( k9_subset_1(A_412,B_413,C_414) = k3_xboole_0(B_413,C_414)
      | ~ m1_subset_1(C_414,k1_zfmisc_1(A_412)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1283,plain,(
    ! [B_413] : k9_subset_1('#skF_3',B_413,'#skF_6') = k3_xboole_0(B_413,'#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_1271])).

tff(c_62,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_106,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_1293,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k3_xboole_0('#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1283,c_1283,c_106])).

tff(c_1593,plain,(
    k7_relat_1('#skF_7',k3_xboole_0('#skF_5','#skF_6')) != k7_relat_1('#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1441,c_1438,c_1293])).

tff(c_1680,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) != k7_relat_1('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1679,c_1679,c_1593])).

tff(c_1683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_1229,c_1680])).

tff(c_1684,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1933,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1684])).

tff(c_5194,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5183,c_1933])).

tff(c_5208,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_1898,c_1928,c_3140,c_1996,c_3140,c_1996,c_3544,c_5194])).

tff(c_5210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_5208])).

tff(c_5211,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1684])).

tff(c_8615,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8606,c_5211])).

tff(c_8626,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_1898,c_1928,c_6603,c_5275,c_6603,c_5275,c_6980,c_8615])).

tff(c_8628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_8626])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.28/3.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.28/3.26  
% 9.28/3.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.28/3.26  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 9.28/3.26  
% 9.28/3.26  %Foreground sorts:
% 9.28/3.26  
% 9.28/3.26  
% 9.28/3.26  %Background operators:
% 9.28/3.26  
% 9.28/3.26  
% 9.28/3.26  %Foreground operators:
% 9.28/3.26  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 9.28/3.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.28/3.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.28/3.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.28/3.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.28/3.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.28/3.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.28/3.26  tff('#skF_7', type, '#skF_7': $i).
% 9.28/3.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.28/3.26  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.28/3.26  tff('#skF_5', type, '#skF_5': $i).
% 9.28/3.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.28/3.26  tff('#skF_6', type, '#skF_6': $i).
% 9.28/3.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.28/3.26  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.28/3.26  tff('#skF_3', type, '#skF_3': $i).
% 9.28/3.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.28/3.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.28/3.26  tff('#skF_8', type, '#skF_8': $i).
% 9.28/3.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.28/3.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.28/3.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.28/3.26  tff('#skF_4', type, '#skF_4': $i).
% 9.28/3.26  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.28/3.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.28/3.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.28/3.26  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.28/3.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.28/3.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.28/3.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.28/3.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.28/3.26  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.28/3.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.28/3.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.28/3.26  
% 9.55/3.29  tff(f_255, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 9.55/3.29  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.55/3.29  tff(f_80, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.55/3.29  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.55/3.29  tff(f_58, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.55/3.29  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.55/3.29  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 9.55/3.29  tff(f_97, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 9.55/3.29  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.55/3.29  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 9.55/3.29  tff(f_213, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 9.55/3.29  tff(f_131, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.55/3.29  tff(f_179, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 9.55/3.29  tff(f_40, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 9.55/3.29  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.55/3.29  tff(f_125, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 9.55/3.29  tff(f_117, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 9.55/3.29  tff(c_88, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.55/3.29  tff(c_82, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.55/3.29  tff(c_78, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.55/3.29  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.55/3.29  tff(c_28, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.55/3.29  tff(c_64, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.55/3.29  tff(c_1707, plain, (![B_472, A_473]: (v1_relat_1(B_472) | ~m1_subset_1(B_472, k1_zfmisc_1(A_473)) | ~v1_relat_1(A_473))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.55/3.29  tff(c_1713, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_1707])).
% 9.55/3.29  tff(c_1725, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1713])).
% 9.55/3.29  tff(c_1728, plain, (![A_474, B_475]: (r2_hidden('#skF_2'(A_474, B_475), A_474) | r1_xboole_0(A_474, B_475))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.55/3.29  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.55/3.29  tff(c_1732, plain, (![A_474, B_475]: (~v1_xboole_0(A_474) | r1_xboole_0(A_474, B_475))), inference(resolution, [status(thm)], [c_1728, c_2])).
% 9.55/3.29  tff(c_1858, plain, (![A_504, B_505]: (k7_relat_1(A_504, B_505)=k1_xboole_0 | ~r1_xboole_0(B_505, k1_relat_1(A_504)) | ~v1_relat_1(A_504))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.55/3.29  tff(c_1884, plain, (![A_506, A_507]: (k7_relat_1(A_506, A_507)=k1_xboole_0 | ~v1_relat_1(A_506) | ~v1_xboole_0(A_507))), inference(resolution, [status(thm)], [c_1732, c_1858])).
% 9.55/3.29  tff(c_1894, plain, (![A_508]: (k7_relat_1('#skF_8', A_508)=k1_xboole_0 | ~v1_xboole_0(A_508))), inference(resolution, [status(thm)], [c_1725, c_1884])).
% 9.55/3.29  tff(c_1898, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1894])).
% 9.55/3.29  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.55/3.29  tff(c_1710, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_70, c_1707])).
% 9.55/3.29  tff(c_1722, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1710])).
% 9.55/3.29  tff(c_1924, plain, (![A_511]: (k7_relat_1('#skF_7', A_511)=k1_xboole_0 | ~v1_xboole_0(A_511))), inference(resolution, [status(thm)], [c_1722, c_1884])).
% 9.55/3.29  tff(c_1928, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1924])).
% 9.55/3.29  tff(c_84, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.55/3.29  tff(c_80, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.55/3.29  tff(c_76, plain, (r1_subset_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.55/3.29  tff(c_1846, plain, (![A_501, B_502]: (r1_xboole_0(A_501, B_502) | ~r1_subset_1(A_501, B_502) | v1_xboole_0(B_502) | v1_xboole_0(A_501))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.55/3.29  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.55/3.29  tff(c_6587, plain, (![A_1105, B_1106]: (k3_xboole_0(A_1105, B_1106)=k1_xboole_0 | ~r1_subset_1(A_1105, B_1106) | v1_xboole_0(B_1106) | v1_xboole_0(A_1105))), inference(resolution, [status(thm)], [c_1846, c_6])).
% 9.55/3.29  tff(c_6596, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_6587])).
% 9.55/3.29  tff(c_6603, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_84, c_80, c_6596])).
% 9.55/3.29  tff(c_5263, plain, (![A_986, B_987, C_988]: (k9_subset_1(A_986, B_987, C_988)=k3_xboole_0(B_987, C_988) | ~m1_subset_1(C_988, k1_zfmisc_1(A_986)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.55/3.29  tff(c_5275, plain, (![B_987]: (k9_subset_1('#skF_3', B_987, '#skF_6')=k3_xboole_0(B_987, '#skF_6'))), inference(resolution, [status(thm)], [c_78, c_5263])).
% 9.55/3.29  tff(c_74, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.55/3.29  tff(c_72, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.55/3.29  tff(c_86, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.55/3.29  tff(c_68, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.55/3.29  tff(c_66, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.55/3.29  tff(c_6714, plain, (![C_1124, A_1122, F_1123, E_1120, D_1121, B_1119]: (v1_funct_1(k1_tmap_1(A_1122, B_1119, C_1124, D_1121, E_1120, F_1123)) | ~m1_subset_1(F_1123, k1_zfmisc_1(k2_zfmisc_1(D_1121, B_1119))) | ~v1_funct_2(F_1123, D_1121, B_1119) | ~v1_funct_1(F_1123) | ~m1_subset_1(E_1120, k1_zfmisc_1(k2_zfmisc_1(C_1124, B_1119))) | ~v1_funct_2(E_1120, C_1124, B_1119) | ~v1_funct_1(E_1120) | ~m1_subset_1(D_1121, k1_zfmisc_1(A_1122)) | v1_xboole_0(D_1121) | ~m1_subset_1(C_1124, k1_zfmisc_1(A_1122)) | v1_xboole_0(C_1124) | v1_xboole_0(B_1119) | v1_xboole_0(A_1122))), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.55/3.29  tff(c_6718, plain, (![A_1122, C_1124, E_1120]: (v1_funct_1(k1_tmap_1(A_1122, '#skF_4', C_1124, '#skF_6', E_1120, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_1120, k1_zfmisc_1(k2_zfmisc_1(C_1124, '#skF_4'))) | ~v1_funct_2(E_1120, C_1124, '#skF_4') | ~v1_funct_1(E_1120) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1122)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1124, k1_zfmisc_1(A_1122)) | v1_xboole_0(C_1124) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1122))), inference(resolution, [status(thm)], [c_64, c_6714])).
% 9.55/3.29  tff(c_6725, plain, (![A_1122, C_1124, E_1120]: (v1_funct_1(k1_tmap_1(A_1122, '#skF_4', C_1124, '#skF_6', E_1120, '#skF_8')) | ~m1_subset_1(E_1120, k1_zfmisc_1(k2_zfmisc_1(C_1124, '#skF_4'))) | ~v1_funct_2(E_1120, C_1124, '#skF_4') | ~v1_funct_1(E_1120) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1122)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1124, k1_zfmisc_1(A_1122)) | v1_xboole_0(C_1124) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1122))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_6718])).
% 9.55/3.29  tff(c_6771, plain, (![A_1128, C_1129, E_1130]: (v1_funct_1(k1_tmap_1(A_1128, '#skF_4', C_1129, '#skF_6', E_1130, '#skF_8')) | ~m1_subset_1(E_1130, k1_zfmisc_1(k2_zfmisc_1(C_1129, '#skF_4'))) | ~v1_funct_2(E_1130, C_1129, '#skF_4') | ~v1_funct_1(E_1130) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1128)) | ~m1_subset_1(C_1129, k1_zfmisc_1(A_1128)) | v1_xboole_0(C_1129) | v1_xboole_0(A_1128))), inference(negUnitSimplification, [status(thm)], [c_86, c_80, c_6725])).
% 9.55/3.29  tff(c_6773, plain, (![A_1128]: (v1_funct_1(k1_tmap_1(A_1128, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1128)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1128)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1128))), inference(resolution, [status(thm)], [c_70, c_6771])).
% 9.55/3.29  tff(c_6778, plain, (![A_1128]: (v1_funct_1(k1_tmap_1(A_1128, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1128)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1128)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1128))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_6773])).
% 9.55/3.29  tff(c_6973, plain, (![A_1174]: (v1_funct_1(k1_tmap_1(A_1174, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1174)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1174)) | v1_xboole_0(A_1174))), inference(negUnitSimplification, [status(thm)], [c_84, c_6778])).
% 9.55/3.29  tff(c_6976, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_6973])).
% 9.55/3.29  tff(c_6979, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_6976])).
% 9.55/3.29  tff(c_6980, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_88, c_6979])).
% 9.55/3.29  tff(c_6509, plain, (![A_1095, B_1096, C_1097, D_1098]: (k2_partfun1(A_1095, B_1096, C_1097, D_1098)=k7_relat_1(C_1097, D_1098) | ~m1_subset_1(C_1097, k1_zfmisc_1(k2_zfmisc_1(A_1095, B_1096))) | ~v1_funct_1(C_1097))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.55/3.29  tff(c_6511, plain, (![D_1098]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_1098)=k7_relat_1('#skF_7', D_1098) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_6509])).
% 9.55/3.29  tff(c_6516, plain, (![D_1098]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_1098)=k7_relat_1('#skF_7', D_1098))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6511])).
% 9.55/3.29  tff(c_6513, plain, (![D_1098]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_1098)=k7_relat_1('#skF_8', D_1098) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_64, c_6509])).
% 9.55/3.29  tff(c_6519, plain, (![D_1098]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_1098)=k7_relat_1('#skF_8', D_1098))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_6513])).
% 9.55/3.29  tff(c_58, plain, (![F_177, D_175, A_172, C_174, E_176, B_173]: (v1_funct_2(k1_tmap_1(A_172, B_173, C_174, D_175, E_176, F_177), k4_subset_1(A_172, C_174, D_175), B_173) | ~m1_subset_1(F_177, k1_zfmisc_1(k2_zfmisc_1(D_175, B_173))) | ~v1_funct_2(F_177, D_175, B_173) | ~v1_funct_1(F_177) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(C_174, B_173))) | ~v1_funct_2(E_176, C_174, B_173) | ~v1_funct_1(E_176) | ~m1_subset_1(D_175, k1_zfmisc_1(A_172)) | v1_xboole_0(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(A_172)) | v1_xboole_0(C_174) | v1_xboole_0(B_173) | v1_xboole_0(A_172))), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.55/3.29  tff(c_56, plain, (![F_177, D_175, A_172, C_174, E_176, B_173]: (m1_subset_1(k1_tmap_1(A_172, B_173, C_174, D_175, E_176, F_177), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_172, C_174, D_175), B_173))) | ~m1_subset_1(F_177, k1_zfmisc_1(k2_zfmisc_1(D_175, B_173))) | ~v1_funct_2(F_177, D_175, B_173) | ~v1_funct_1(F_177) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(C_174, B_173))) | ~v1_funct_2(E_176, C_174, B_173) | ~v1_funct_1(E_176) | ~m1_subset_1(D_175, k1_zfmisc_1(A_172)) | v1_xboole_0(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(A_172)) | v1_xboole_0(C_174) | v1_xboole_0(B_173) | v1_xboole_0(A_172))), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.55/3.29  tff(c_7136, plain, (![E_1213, C_1214, A_1212, B_1215, D_1211, F_1216]: (k2_partfun1(k4_subset_1(A_1212, C_1214, D_1211), B_1215, k1_tmap_1(A_1212, B_1215, C_1214, D_1211, E_1213, F_1216), C_1214)=E_1213 | ~m1_subset_1(k1_tmap_1(A_1212, B_1215, C_1214, D_1211, E_1213, F_1216), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1212, C_1214, D_1211), B_1215))) | ~v1_funct_2(k1_tmap_1(A_1212, B_1215, C_1214, D_1211, E_1213, F_1216), k4_subset_1(A_1212, C_1214, D_1211), B_1215) | ~v1_funct_1(k1_tmap_1(A_1212, B_1215, C_1214, D_1211, E_1213, F_1216)) | k2_partfun1(D_1211, B_1215, F_1216, k9_subset_1(A_1212, C_1214, D_1211))!=k2_partfun1(C_1214, B_1215, E_1213, k9_subset_1(A_1212, C_1214, D_1211)) | ~m1_subset_1(F_1216, k1_zfmisc_1(k2_zfmisc_1(D_1211, B_1215))) | ~v1_funct_2(F_1216, D_1211, B_1215) | ~v1_funct_1(F_1216) | ~m1_subset_1(E_1213, k1_zfmisc_1(k2_zfmisc_1(C_1214, B_1215))) | ~v1_funct_2(E_1213, C_1214, B_1215) | ~v1_funct_1(E_1213) | ~m1_subset_1(D_1211, k1_zfmisc_1(A_1212)) | v1_xboole_0(D_1211) | ~m1_subset_1(C_1214, k1_zfmisc_1(A_1212)) | v1_xboole_0(C_1214) | v1_xboole_0(B_1215) | v1_xboole_0(A_1212))), inference(cnfTransformation, [status(thm)], [f_179])).
% 9.55/3.29  tff(c_7543, plain, (![D_1299, A_1300, E_1298, F_1301, C_1302, B_1297]: (k2_partfun1(k4_subset_1(A_1300, C_1302, D_1299), B_1297, k1_tmap_1(A_1300, B_1297, C_1302, D_1299, E_1298, F_1301), C_1302)=E_1298 | ~v1_funct_2(k1_tmap_1(A_1300, B_1297, C_1302, D_1299, E_1298, F_1301), k4_subset_1(A_1300, C_1302, D_1299), B_1297) | ~v1_funct_1(k1_tmap_1(A_1300, B_1297, C_1302, D_1299, E_1298, F_1301)) | k2_partfun1(D_1299, B_1297, F_1301, k9_subset_1(A_1300, C_1302, D_1299))!=k2_partfun1(C_1302, B_1297, E_1298, k9_subset_1(A_1300, C_1302, D_1299)) | ~m1_subset_1(F_1301, k1_zfmisc_1(k2_zfmisc_1(D_1299, B_1297))) | ~v1_funct_2(F_1301, D_1299, B_1297) | ~v1_funct_1(F_1301) | ~m1_subset_1(E_1298, k1_zfmisc_1(k2_zfmisc_1(C_1302, B_1297))) | ~v1_funct_2(E_1298, C_1302, B_1297) | ~v1_funct_1(E_1298) | ~m1_subset_1(D_1299, k1_zfmisc_1(A_1300)) | v1_xboole_0(D_1299) | ~m1_subset_1(C_1302, k1_zfmisc_1(A_1300)) | v1_xboole_0(C_1302) | v1_xboole_0(B_1297) | v1_xboole_0(A_1300))), inference(resolution, [status(thm)], [c_56, c_7136])).
% 9.55/3.29  tff(c_8152, plain, (![D_1369, B_1367, F_1371, C_1372, A_1370, E_1368]: (k2_partfun1(k4_subset_1(A_1370, C_1372, D_1369), B_1367, k1_tmap_1(A_1370, B_1367, C_1372, D_1369, E_1368, F_1371), C_1372)=E_1368 | ~v1_funct_1(k1_tmap_1(A_1370, B_1367, C_1372, D_1369, E_1368, F_1371)) | k2_partfun1(D_1369, B_1367, F_1371, k9_subset_1(A_1370, C_1372, D_1369))!=k2_partfun1(C_1372, B_1367, E_1368, k9_subset_1(A_1370, C_1372, D_1369)) | ~m1_subset_1(F_1371, k1_zfmisc_1(k2_zfmisc_1(D_1369, B_1367))) | ~v1_funct_2(F_1371, D_1369, B_1367) | ~v1_funct_1(F_1371) | ~m1_subset_1(E_1368, k1_zfmisc_1(k2_zfmisc_1(C_1372, B_1367))) | ~v1_funct_2(E_1368, C_1372, B_1367) | ~v1_funct_1(E_1368) | ~m1_subset_1(D_1369, k1_zfmisc_1(A_1370)) | v1_xboole_0(D_1369) | ~m1_subset_1(C_1372, k1_zfmisc_1(A_1370)) | v1_xboole_0(C_1372) | v1_xboole_0(B_1367) | v1_xboole_0(A_1370))), inference(resolution, [status(thm)], [c_58, c_7543])).
% 9.55/3.29  tff(c_8158, plain, (![A_1370, C_1372, E_1368]: (k2_partfun1(k4_subset_1(A_1370, C_1372, '#skF_6'), '#skF_4', k1_tmap_1(A_1370, '#skF_4', C_1372, '#skF_6', E_1368, '#skF_8'), C_1372)=E_1368 | ~v1_funct_1(k1_tmap_1(A_1370, '#skF_4', C_1372, '#skF_6', E_1368, '#skF_8')) | k2_partfun1(C_1372, '#skF_4', E_1368, k9_subset_1(A_1370, C_1372, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_1370, C_1372, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_1368, k1_zfmisc_1(k2_zfmisc_1(C_1372, '#skF_4'))) | ~v1_funct_2(E_1368, C_1372, '#skF_4') | ~v1_funct_1(E_1368) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1370)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1372, k1_zfmisc_1(A_1370)) | v1_xboole_0(C_1372) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1370))), inference(resolution, [status(thm)], [c_64, c_8152])).
% 9.55/3.29  tff(c_8166, plain, (![A_1370, C_1372, E_1368]: (k2_partfun1(k4_subset_1(A_1370, C_1372, '#skF_6'), '#skF_4', k1_tmap_1(A_1370, '#skF_4', C_1372, '#skF_6', E_1368, '#skF_8'), C_1372)=E_1368 | ~v1_funct_1(k1_tmap_1(A_1370, '#skF_4', C_1372, '#skF_6', E_1368, '#skF_8')) | k2_partfun1(C_1372, '#skF_4', E_1368, k9_subset_1(A_1370, C_1372, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1370, C_1372, '#skF_6')) | ~m1_subset_1(E_1368, k1_zfmisc_1(k2_zfmisc_1(C_1372, '#skF_4'))) | ~v1_funct_2(E_1368, C_1372, '#skF_4') | ~v1_funct_1(E_1368) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1370)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1372, k1_zfmisc_1(A_1370)) | v1_xboole_0(C_1372) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1370))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_6519, c_8158])).
% 9.55/3.29  tff(c_8569, plain, (![A_1421, C_1422, E_1423]: (k2_partfun1(k4_subset_1(A_1421, C_1422, '#skF_6'), '#skF_4', k1_tmap_1(A_1421, '#skF_4', C_1422, '#skF_6', E_1423, '#skF_8'), C_1422)=E_1423 | ~v1_funct_1(k1_tmap_1(A_1421, '#skF_4', C_1422, '#skF_6', E_1423, '#skF_8')) | k2_partfun1(C_1422, '#skF_4', E_1423, k9_subset_1(A_1421, C_1422, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1421, C_1422, '#skF_6')) | ~m1_subset_1(E_1423, k1_zfmisc_1(k2_zfmisc_1(C_1422, '#skF_4'))) | ~v1_funct_2(E_1423, C_1422, '#skF_4') | ~v1_funct_1(E_1423) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1421)) | ~m1_subset_1(C_1422, k1_zfmisc_1(A_1421)) | v1_xboole_0(C_1422) | v1_xboole_0(A_1421))), inference(negUnitSimplification, [status(thm)], [c_86, c_80, c_8166])).
% 9.55/3.29  tff(c_8574, plain, (![A_1421]: (k2_partfun1(k4_subset_1(A_1421, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1421, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1421, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_1421, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1421, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1421)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1421)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1421))), inference(resolution, [status(thm)], [c_70, c_8569])).
% 9.55/3.29  tff(c_8582, plain, (![A_1421]: (k2_partfun1(k4_subset_1(A_1421, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1421, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1421, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_1421, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1421, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1421)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1421)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1421))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_6516, c_8574])).
% 9.55/3.29  tff(c_8606, plain, (![A_1424]: (k2_partfun1(k4_subset_1(A_1424, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1424, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1424, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_1424, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1424, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1424)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1424)) | v1_xboole_0(A_1424))), inference(negUnitSimplification, [status(thm)], [c_84, c_8582])).
% 9.55/3.29  tff(c_3128, plain, (![A_632, B_633]: (k3_xboole_0(A_632, B_633)=k1_xboole_0 | ~r1_subset_1(A_632, B_633) | v1_xboole_0(B_633) | v1_xboole_0(A_632))), inference(resolution, [status(thm)], [c_1846, c_6])).
% 9.55/3.29  tff(c_3134, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_3128])).
% 9.55/3.29  tff(c_3140, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_84, c_80, c_3134])).
% 9.55/3.29  tff(c_1984, plain, (![A_525, B_526, C_527]: (k9_subset_1(A_525, B_526, C_527)=k3_xboole_0(B_526, C_527) | ~m1_subset_1(C_527, k1_zfmisc_1(A_525)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.55/3.29  tff(c_1996, plain, (![B_526]: (k9_subset_1('#skF_3', B_526, '#skF_6')=k3_xboole_0(B_526, '#skF_6'))), inference(resolution, [status(thm)], [c_78, c_1984])).
% 9.55/3.29  tff(c_3257, plain, (![D_645, F_647, E_644, C_648, B_643, A_646]: (v1_funct_1(k1_tmap_1(A_646, B_643, C_648, D_645, E_644, F_647)) | ~m1_subset_1(F_647, k1_zfmisc_1(k2_zfmisc_1(D_645, B_643))) | ~v1_funct_2(F_647, D_645, B_643) | ~v1_funct_1(F_647) | ~m1_subset_1(E_644, k1_zfmisc_1(k2_zfmisc_1(C_648, B_643))) | ~v1_funct_2(E_644, C_648, B_643) | ~v1_funct_1(E_644) | ~m1_subset_1(D_645, k1_zfmisc_1(A_646)) | v1_xboole_0(D_645) | ~m1_subset_1(C_648, k1_zfmisc_1(A_646)) | v1_xboole_0(C_648) | v1_xboole_0(B_643) | v1_xboole_0(A_646))), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.55/3.29  tff(c_3261, plain, (![A_646, C_648, E_644]: (v1_funct_1(k1_tmap_1(A_646, '#skF_4', C_648, '#skF_6', E_644, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_644, k1_zfmisc_1(k2_zfmisc_1(C_648, '#skF_4'))) | ~v1_funct_2(E_644, C_648, '#skF_4') | ~v1_funct_1(E_644) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_646)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_648, k1_zfmisc_1(A_646)) | v1_xboole_0(C_648) | v1_xboole_0('#skF_4') | v1_xboole_0(A_646))), inference(resolution, [status(thm)], [c_64, c_3257])).
% 9.55/3.29  tff(c_3268, plain, (![A_646, C_648, E_644]: (v1_funct_1(k1_tmap_1(A_646, '#skF_4', C_648, '#skF_6', E_644, '#skF_8')) | ~m1_subset_1(E_644, k1_zfmisc_1(k2_zfmisc_1(C_648, '#skF_4'))) | ~v1_funct_2(E_644, C_648, '#skF_4') | ~v1_funct_1(E_644) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_646)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_648, k1_zfmisc_1(A_646)) | v1_xboole_0(C_648) | v1_xboole_0('#skF_4') | v1_xboole_0(A_646))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_3261])).
% 9.55/3.29  tff(c_3322, plain, (![A_653, C_654, E_655]: (v1_funct_1(k1_tmap_1(A_653, '#skF_4', C_654, '#skF_6', E_655, '#skF_8')) | ~m1_subset_1(E_655, k1_zfmisc_1(k2_zfmisc_1(C_654, '#skF_4'))) | ~v1_funct_2(E_655, C_654, '#skF_4') | ~v1_funct_1(E_655) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_653)) | ~m1_subset_1(C_654, k1_zfmisc_1(A_653)) | v1_xboole_0(C_654) | v1_xboole_0(A_653))), inference(negUnitSimplification, [status(thm)], [c_86, c_80, c_3268])).
% 9.55/3.29  tff(c_3324, plain, (![A_653]: (v1_funct_1(k1_tmap_1(A_653, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_653)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_653)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_653))), inference(resolution, [status(thm)], [c_70, c_3322])).
% 9.55/3.29  tff(c_3329, plain, (![A_653]: (v1_funct_1(k1_tmap_1(A_653, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_653)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_653)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_653))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3324])).
% 9.55/3.29  tff(c_3537, plain, (![A_694]: (v1_funct_1(k1_tmap_1(A_694, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_694)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_694)) | v1_xboole_0(A_694))), inference(negUnitSimplification, [status(thm)], [c_84, c_3329])).
% 9.55/3.29  tff(c_3540, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_3537])).
% 9.55/3.29  tff(c_3543, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3540])).
% 9.55/3.29  tff(c_3544, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_88, c_3543])).
% 9.55/3.29  tff(c_2986, plain, (![A_618, B_619, C_620, D_621]: (k2_partfun1(A_618, B_619, C_620, D_621)=k7_relat_1(C_620, D_621) | ~m1_subset_1(C_620, k1_zfmisc_1(k2_zfmisc_1(A_618, B_619))) | ~v1_funct_1(C_620))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.55/3.29  tff(c_2988, plain, (![D_621]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_621)=k7_relat_1('#skF_7', D_621) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_2986])).
% 9.55/3.29  tff(c_2993, plain, (![D_621]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_621)=k7_relat_1('#skF_7', D_621))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2988])).
% 9.55/3.29  tff(c_2990, plain, (![D_621]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_621)=k7_relat_1('#skF_8', D_621) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_64, c_2986])).
% 9.55/3.29  tff(c_2996, plain, (![D_621]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_621)=k7_relat_1('#skF_8', D_621))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2990])).
% 9.55/3.29  tff(c_3581, plain, (![A_705, E_706, F_709, C_707, D_704, B_708]: (k2_partfun1(k4_subset_1(A_705, C_707, D_704), B_708, k1_tmap_1(A_705, B_708, C_707, D_704, E_706, F_709), D_704)=F_709 | ~m1_subset_1(k1_tmap_1(A_705, B_708, C_707, D_704, E_706, F_709), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_705, C_707, D_704), B_708))) | ~v1_funct_2(k1_tmap_1(A_705, B_708, C_707, D_704, E_706, F_709), k4_subset_1(A_705, C_707, D_704), B_708) | ~v1_funct_1(k1_tmap_1(A_705, B_708, C_707, D_704, E_706, F_709)) | k2_partfun1(D_704, B_708, F_709, k9_subset_1(A_705, C_707, D_704))!=k2_partfun1(C_707, B_708, E_706, k9_subset_1(A_705, C_707, D_704)) | ~m1_subset_1(F_709, k1_zfmisc_1(k2_zfmisc_1(D_704, B_708))) | ~v1_funct_2(F_709, D_704, B_708) | ~v1_funct_1(F_709) | ~m1_subset_1(E_706, k1_zfmisc_1(k2_zfmisc_1(C_707, B_708))) | ~v1_funct_2(E_706, C_707, B_708) | ~v1_funct_1(E_706) | ~m1_subset_1(D_704, k1_zfmisc_1(A_705)) | v1_xboole_0(D_704) | ~m1_subset_1(C_707, k1_zfmisc_1(A_705)) | v1_xboole_0(C_707) | v1_xboole_0(B_708) | v1_xboole_0(A_705))), inference(cnfTransformation, [status(thm)], [f_179])).
% 9.55/3.29  tff(c_4229, plain, (![B_858, A_861, C_863, E_859, F_862, D_860]: (k2_partfun1(k4_subset_1(A_861, C_863, D_860), B_858, k1_tmap_1(A_861, B_858, C_863, D_860, E_859, F_862), D_860)=F_862 | ~v1_funct_2(k1_tmap_1(A_861, B_858, C_863, D_860, E_859, F_862), k4_subset_1(A_861, C_863, D_860), B_858) | ~v1_funct_1(k1_tmap_1(A_861, B_858, C_863, D_860, E_859, F_862)) | k2_partfun1(D_860, B_858, F_862, k9_subset_1(A_861, C_863, D_860))!=k2_partfun1(C_863, B_858, E_859, k9_subset_1(A_861, C_863, D_860)) | ~m1_subset_1(F_862, k1_zfmisc_1(k2_zfmisc_1(D_860, B_858))) | ~v1_funct_2(F_862, D_860, B_858) | ~v1_funct_1(F_862) | ~m1_subset_1(E_859, k1_zfmisc_1(k2_zfmisc_1(C_863, B_858))) | ~v1_funct_2(E_859, C_863, B_858) | ~v1_funct_1(E_859) | ~m1_subset_1(D_860, k1_zfmisc_1(A_861)) | v1_xboole_0(D_860) | ~m1_subset_1(C_863, k1_zfmisc_1(A_861)) | v1_xboole_0(C_863) | v1_xboole_0(B_858) | v1_xboole_0(A_861))), inference(resolution, [status(thm)], [c_56, c_3581])).
% 9.55/3.29  tff(c_4818, plain, (![C_923, A_921, E_919, B_918, D_920, F_922]: (k2_partfun1(k4_subset_1(A_921, C_923, D_920), B_918, k1_tmap_1(A_921, B_918, C_923, D_920, E_919, F_922), D_920)=F_922 | ~v1_funct_1(k1_tmap_1(A_921, B_918, C_923, D_920, E_919, F_922)) | k2_partfun1(D_920, B_918, F_922, k9_subset_1(A_921, C_923, D_920))!=k2_partfun1(C_923, B_918, E_919, k9_subset_1(A_921, C_923, D_920)) | ~m1_subset_1(F_922, k1_zfmisc_1(k2_zfmisc_1(D_920, B_918))) | ~v1_funct_2(F_922, D_920, B_918) | ~v1_funct_1(F_922) | ~m1_subset_1(E_919, k1_zfmisc_1(k2_zfmisc_1(C_923, B_918))) | ~v1_funct_2(E_919, C_923, B_918) | ~v1_funct_1(E_919) | ~m1_subset_1(D_920, k1_zfmisc_1(A_921)) | v1_xboole_0(D_920) | ~m1_subset_1(C_923, k1_zfmisc_1(A_921)) | v1_xboole_0(C_923) | v1_xboole_0(B_918) | v1_xboole_0(A_921))), inference(resolution, [status(thm)], [c_58, c_4229])).
% 9.55/3.29  tff(c_4824, plain, (![A_921, C_923, E_919]: (k2_partfun1(k4_subset_1(A_921, C_923, '#skF_6'), '#skF_4', k1_tmap_1(A_921, '#skF_4', C_923, '#skF_6', E_919, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_921, '#skF_4', C_923, '#skF_6', E_919, '#skF_8')) | k2_partfun1(C_923, '#skF_4', E_919, k9_subset_1(A_921, C_923, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_921, C_923, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_919, k1_zfmisc_1(k2_zfmisc_1(C_923, '#skF_4'))) | ~v1_funct_2(E_919, C_923, '#skF_4') | ~v1_funct_1(E_919) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_921)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_923, k1_zfmisc_1(A_921)) | v1_xboole_0(C_923) | v1_xboole_0('#skF_4') | v1_xboole_0(A_921))), inference(resolution, [status(thm)], [c_64, c_4818])).
% 9.55/3.29  tff(c_4832, plain, (![A_921, C_923, E_919]: (k2_partfun1(k4_subset_1(A_921, C_923, '#skF_6'), '#skF_4', k1_tmap_1(A_921, '#skF_4', C_923, '#skF_6', E_919, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_921, '#skF_4', C_923, '#skF_6', E_919, '#skF_8')) | k2_partfun1(C_923, '#skF_4', E_919, k9_subset_1(A_921, C_923, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_921, C_923, '#skF_6')) | ~m1_subset_1(E_919, k1_zfmisc_1(k2_zfmisc_1(C_923, '#skF_4'))) | ~v1_funct_2(E_919, C_923, '#skF_4') | ~v1_funct_1(E_919) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_921)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_923, k1_zfmisc_1(A_921)) | v1_xboole_0(C_923) | v1_xboole_0('#skF_4') | v1_xboole_0(A_921))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_2996, c_4824])).
% 9.55/3.29  tff(c_5129, plain, (![A_968, C_969, E_970]: (k2_partfun1(k4_subset_1(A_968, C_969, '#skF_6'), '#skF_4', k1_tmap_1(A_968, '#skF_4', C_969, '#skF_6', E_970, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_968, '#skF_4', C_969, '#skF_6', E_970, '#skF_8')) | k2_partfun1(C_969, '#skF_4', E_970, k9_subset_1(A_968, C_969, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_968, C_969, '#skF_6')) | ~m1_subset_1(E_970, k1_zfmisc_1(k2_zfmisc_1(C_969, '#skF_4'))) | ~v1_funct_2(E_970, C_969, '#skF_4') | ~v1_funct_1(E_970) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_968)) | ~m1_subset_1(C_969, k1_zfmisc_1(A_968)) | v1_xboole_0(C_969) | v1_xboole_0(A_968))), inference(negUnitSimplification, [status(thm)], [c_86, c_80, c_4832])).
% 9.55/3.29  tff(c_5134, plain, (![A_968]: (k2_partfun1(k4_subset_1(A_968, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_968, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_968, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_968, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_968, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_968)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_968)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_968))), inference(resolution, [status(thm)], [c_70, c_5129])).
% 9.55/3.29  tff(c_5142, plain, (![A_968]: (k2_partfun1(k4_subset_1(A_968, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_968, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_968, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_968, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_968, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_968)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_968)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_968))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2993, c_5134])).
% 9.55/3.29  tff(c_5183, plain, (![A_972]: (k2_partfun1(k4_subset_1(A_972, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_972, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_972, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_972, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_972, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_972)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_972)) | v1_xboole_0(A_972))), inference(negUnitSimplification, [status(thm)], [c_84, c_5142])).
% 9.55/3.29  tff(c_124, plain, (![A_250, B_251]: (r2_hidden('#skF_2'(A_250, B_251), B_251) | r1_xboole_0(A_250, B_251))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.55/3.29  tff(c_129, plain, (![B_252, A_253]: (~v1_xboole_0(B_252) | r1_xboole_0(A_253, B_252))), inference(resolution, [status(thm)], [c_124, c_2])).
% 9.55/3.29  tff(c_12, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.55/3.29  tff(c_136, plain, (![B_252, A_253]: (r1_xboole_0(B_252, A_253) | ~v1_xboole_0(B_252))), inference(resolution, [status(thm)], [c_129, c_12])).
% 9.55/3.29  tff(c_201, plain, (![B_266, A_267]: (v1_relat_1(B_266) | ~m1_subset_1(B_266, k1_zfmisc_1(A_267)) | ~v1_relat_1(A_267))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.55/3.29  tff(c_204, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_70, c_201])).
% 9.55/3.29  tff(c_216, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_204])).
% 9.55/3.29  tff(c_232, plain, (![C_270, A_271, B_272]: (v4_relat_1(C_270, A_271) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.55/3.29  tff(c_239, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_232])).
% 9.55/3.29  tff(c_322, plain, (![B_286, A_287]: (k1_relat_1(B_286)=A_287 | ~v1_partfun1(B_286, A_287) | ~v4_relat_1(B_286, A_287) | ~v1_relat_1(B_286))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.55/3.29  tff(c_328, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_239, c_322])).
% 9.55/3.29  tff(c_334, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_328])).
% 9.55/3.29  tff(c_893, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_334])).
% 9.55/3.29  tff(c_1168, plain, (![C_405, A_406, B_407]: (v1_partfun1(C_405, A_406) | ~v1_funct_2(C_405, A_406, B_407) | ~v1_funct_1(C_405) | ~m1_subset_1(C_405, k1_zfmisc_1(k2_zfmisc_1(A_406, B_407))) | v1_xboole_0(B_407))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.55/3.29  tff(c_1171, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_70, c_1168])).
% 9.55/3.29  tff(c_1177, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1171])).
% 9.55/3.29  tff(c_1179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_893, c_1177])).
% 9.55/3.29  tff(c_1180, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_334])).
% 9.55/3.29  tff(c_30, plain, (![A_27, B_29]: (k7_relat_1(A_27, B_29)=k1_xboole_0 | ~r1_xboole_0(B_29, k1_relat_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.55/3.29  tff(c_1185, plain, (![B_29]: (k7_relat_1('#skF_7', B_29)=k1_xboole_0 | ~r1_xboole_0(B_29, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1180, c_30])).
% 9.55/3.29  tff(c_1234, plain, (![B_410]: (k7_relat_1('#skF_7', B_410)=k1_xboole_0 | ~r1_xboole_0(B_410, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_1185])).
% 9.55/3.29  tff(c_1262, plain, (![B_411]: (k7_relat_1('#skF_7', B_411)=k1_xboole_0 | ~v1_xboole_0(B_411))), inference(resolution, [status(thm)], [c_136, c_1234])).
% 9.55/3.29  tff(c_1266, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1262])).
% 9.55/3.29  tff(c_207, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_201])).
% 9.55/3.29  tff(c_219, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_207])).
% 9.55/3.29  tff(c_240, plain, (v4_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_232])).
% 9.55/3.29  tff(c_325, plain, (k1_relat_1('#skF_8')='#skF_6' | ~v1_partfun1('#skF_8', '#skF_6') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_240, c_322])).
% 9.55/3.29  tff(c_331, plain, (k1_relat_1('#skF_8')='#skF_6' | ~v1_partfun1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_325])).
% 9.55/3.29  tff(c_335, plain, (~v1_partfun1('#skF_8', '#skF_6')), inference(splitLeft, [status(thm)], [c_331])).
% 9.55/3.29  tff(c_860, plain, (![C_367, A_368, B_369]: (v1_partfun1(C_367, A_368) | ~v1_funct_2(C_367, A_368, B_369) | ~v1_funct_1(C_367) | ~m1_subset_1(C_367, k1_zfmisc_1(k2_zfmisc_1(A_368, B_369))) | v1_xboole_0(B_369))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.55/3.29  tff(c_866, plain, (v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_860])).
% 9.55/3.29  tff(c_873, plain, (v1_partfun1('#skF_8', '#skF_6') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_866])).
% 9.55/3.29  tff(c_875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_335, c_873])).
% 9.55/3.29  tff(c_876, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_331])).
% 9.55/3.29  tff(c_881, plain, (![B_29]: (k7_relat_1('#skF_8', B_29)=k1_xboole_0 | ~r1_xboole_0(B_29, '#skF_6') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_876, c_30])).
% 9.55/3.29  tff(c_1197, plain, (![B_408]: (k7_relat_1('#skF_8', B_408)=k1_xboole_0 | ~r1_xboole_0(B_408, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_881])).
% 9.55/3.29  tff(c_1225, plain, (![B_409]: (k7_relat_1('#skF_8', B_409)=k1_xboole_0 | ~v1_xboole_0(B_409))), inference(resolution, [status(thm)], [c_136, c_1197])).
% 9.55/3.29  tff(c_1229, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1225])).
% 9.55/3.29  tff(c_281, plain, (![A_282, B_283]: (r1_xboole_0(A_282, B_283) | ~r1_subset_1(A_282, B_283) | v1_xboole_0(B_283) | v1_xboole_0(A_282))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.55/3.29  tff(c_1667, plain, (![A_464, B_465]: (k3_xboole_0(A_464, B_465)=k1_xboole_0 | ~r1_subset_1(A_464, B_465) | v1_xboole_0(B_465) | v1_xboole_0(A_464))), inference(resolution, [status(thm)], [c_281, c_6])).
% 9.55/3.29  tff(c_1673, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_1667])).
% 9.55/3.29  tff(c_1679, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_84, c_80, c_1673])).
% 9.55/3.29  tff(c_1431, plain, (![A_427, B_428, C_429, D_430]: (k2_partfun1(A_427, B_428, C_429, D_430)=k7_relat_1(C_429, D_430) | ~m1_subset_1(C_429, k1_zfmisc_1(k2_zfmisc_1(A_427, B_428))) | ~v1_funct_1(C_429))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.55/3.29  tff(c_1435, plain, (![D_430]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_430)=k7_relat_1('#skF_8', D_430) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_64, c_1431])).
% 9.55/3.29  tff(c_1441, plain, (![D_430]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_430)=k7_relat_1('#skF_8', D_430))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1435])).
% 9.55/3.29  tff(c_1433, plain, (![D_430]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_430)=k7_relat_1('#skF_7', D_430) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_1431])).
% 9.55/3.29  tff(c_1438, plain, (![D_430]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_430)=k7_relat_1('#skF_7', D_430))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1433])).
% 9.55/3.29  tff(c_1271, plain, (![A_412, B_413, C_414]: (k9_subset_1(A_412, B_413, C_414)=k3_xboole_0(B_413, C_414) | ~m1_subset_1(C_414, k1_zfmisc_1(A_412)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.55/3.29  tff(c_1283, plain, (![B_413]: (k9_subset_1('#skF_3', B_413, '#skF_6')=k3_xboole_0(B_413, '#skF_6'))), inference(resolution, [status(thm)], [c_78, c_1271])).
% 9.55/3.29  tff(c_62, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.55/3.29  tff(c_106, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_62])).
% 9.55/3.29  tff(c_1293, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k3_xboole_0('#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1283, c_1283, c_106])).
% 9.55/3.29  tff(c_1593, plain, (k7_relat_1('#skF_7', k3_xboole_0('#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1441, c_1438, c_1293])).
% 9.55/3.29  tff(c_1680, plain, (k7_relat_1('#skF_7', k1_xboole_0)!=k7_relat_1('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1679, c_1679, c_1593])).
% 9.55/3.29  tff(c_1683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1266, c_1229, c_1680])).
% 9.55/3.29  tff(c_1684, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_62])).
% 9.55/3.29  tff(c_1933, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitLeft, [status(thm)], [c_1684])).
% 9.55/3.29  tff(c_5194, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5183, c_1933])).
% 9.55/3.29  tff(c_5208, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_1898, c_1928, c_3140, c_1996, c_3140, c_1996, c_3544, c_5194])).
% 9.55/3.29  tff(c_5210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_5208])).
% 9.55/3.29  tff(c_5211, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_1684])).
% 9.55/3.29  tff(c_8615, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8606, c_5211])).
% 9.55/3.29  tff(c_8626, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_1898, c_1928, c_6603, c_5275, c_6603, c_5275, c_6980, c_8615])).
% 9.55/3.29  tff(c_8628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_8626])).
% 9.55/3.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.55/3.29  
% 9.55/3.29  Inference rules
% 9.55/3.29  ----------------------
% 9.55/3.29  #Ref     : 0
% 9.55/3.29  #Sup     : 1771
% 9.55/3.29  #Fact    : 0
% 9.55/3.29  #Define  : 0
% 9.55/3.29  #Split   : 39
% 9.55/3.29  #Chain   : 0
% 9.55/3.29  #Close   : 0
% 9.55/3.29  
% 9.55/3.29  Ordering : KBO
% 9.55/3.29  
% 9.55/3.29  Simplification rules
% 9.55/3.29  ----------------------
% 9.55/3.29  #Subsume      : 282
% 9.55/3.29  #Demod        : 963
% 9.55/3.29  #Tautology    : 842
% 9.55/3.29  #SimpNegUnit  : 366
% 9.55/3.29  #BackRed      : 17
% 9.55/3.29  
% 9.55/3.29  #Partial instantiations: 0
% 9.55/3.29  #Strategies tried      : 1
% 9.55/3.29  
% 9.55/3.29  Timing (in seconds)
% 9.55/3.29  ----------------------
% 9.55/3.30  Preprocessing        : 0.46
% 9.55/3.30  Parsing              : 0.24
% 9.55/3.30  CNF conversion       : 0.06
% 9.55/3.30  Main loop            : 1.97
% 9.55/3.30  Inferencing          : 0.69
% 9.55/3.30  Reduction            : 0.63
% 9.55/3.30  Demodulation         : 0.44
% 9.55/3.30  BG Simplification    : 0.06
% 9.55/3.30  Subsumption          : 0.45
% 9.55/3.30  Abstraction          : 0.07
% 9.55/3.30  MUC search           : 0.00
% 9.55/3.30  Cooper               : 0.00
% 9.55/3.30  Total                : 2.49
% 9.55/3.30  Index Insertion      : 0.00
% 9.55/3.30  Index Deletion       : 0.00
% 9.55/3.30  Index Matching       : 0.00
% 9.55/3.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
