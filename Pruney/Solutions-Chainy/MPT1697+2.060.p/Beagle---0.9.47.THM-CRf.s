%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:18 EST 2020

% Result     : Theorem 48.56s
% Output     : CNFRefutation 48.75s
% Verified   : 
% Statistics : Number of formulae       :  232 (1818 expanded)
%              Number of leaves         :   40 ( 646 expanded)
%              Depth                    :   21
%              Number of atoms          :  708 (8219 expanded)
%              Number of equality atoms :  177 (1860 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_203,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_161,axiom,(
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

tff(f_127,axiom,(
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

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_73,plain,(
    ! [C_223,A_224,B_225] :
      ( v1_relat_1(C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_80,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_73])).

tff(c_1742,plain,(
    ! [C_377,A_378,B_379] :
      ( v4_relat_1(C_377,A_378)
      | ~ m1_subset_1(C_377,k1_zfmisc_1(k2_zfmisc_1(A_378,B_379))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1749,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_1742])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = B_16
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1753,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1749,c_14])).

tff(c_1756,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1753])).

tff(c_1986,plain,(
    ! [C_403,A_404,B_405] :
      ( k7_relat_1(k7_relat_1(C_403,A_404),B_405) = k7_relat_1(C_403,k3_xboole_0(A_404,B_405))
      | ~ v1_relat_1(C_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2019,plain,(
    ! [B_405] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',B_405)) = k7_relat_1('#skF_6',B_405)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1756,c_1986])).

tff(c_2027,plain,(
    ! [B_405] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',B_405)) = k7_relat_1('#skF_6',B_405) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2019])).

tff(c_1785,plain,(
    ! [A_384,B_385,C_386] :
      ( k9_subset_1(A_384,B_385,C_386) = k3_xboole_0(B_385,C_386)
      | ~ m1_subset_1(C_386,k1_zfmisc_1(A_384)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1796,plain,(
    ! [B_385] : k9_subset_1('#skF_1',B_385,'#skF_4') = k3_xboole_0(B_385,'#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1785])).

tff(c_1886,plain,(
    ! [A_396,C_397,B_398] :
      ( k9_subset_1(A_396,C_397,B_398) = k9_subset_1(A_396,B_398,C_397)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(A_396)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1892,plain,(
    ! [B_398] : k9_subset_1('#skF_1',B_398,'#skF_4') = k9_subset_1('#skF_1','#skF_4',B_398) ),
    inference(resolution,[status(thm)],[c_56,c_1886])).

tff(c_1903,plain,(
    ! [B_399] : k9_subset_1('#skF_1','#skF_4',B_399) = k3_xboole_0(B_399,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1796,c_1892])).

tff(c_1797,plain,(
    ! [B_385] : k9_subset_1('#skF_1',B_385,'#skF_3') = k3_xboole_0(B_385,'#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1785])).

tff(c_1910,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1903,c_1797])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_54,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | ~ r1_subset_1(A_17,B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_81,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_73])).

tff(c_1750,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1742])).

tff(c_1759,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1750,c_14])).

tff(c_1762,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1759])).

tff(c_1835,plain,(
    ! [C_391,A_392,B_393] :
      ( k7_relat_1(k7_relat_1(C_391,A_392),B_393) = k1_xboole_0
      | ~ r1_xboole_0(A_392,B_393)
      | ~ v1_relat_1(C_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1850,plain,(
    ! [B_393] :
      ( k7_relat_1('#skF_5',B_393) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_393)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1762,c_1835])).

tff(c_1860,plain,(
    ! [B_394] :
      ( k7_relat_1('#skF_5',B_394) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_394) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1850])).

tff(c_1864,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_5',B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_1860])).

tff(c_2106,plain,(
    ! [B_409] :
      ( k7_relat_1('#skF_5',B_409) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_409)
      | v1_xboole_0(B_409) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1864])).

tff(c_2109,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_2106])).

tff(c_2112,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2109])).

tff(c_2016,plain,(
    ! [B_405] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',B_405)) = k7_relat_1('#skF_5',B_405)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1762,c_1986])).

tff(c_2025,plain,(
    ! [B_405] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',B_405)) = k7_relat_1('#skF_5',B_405) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2016])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_2151,plain,(
    ! [A_411,B_412,C_413,D_414] :
      ( k2_partfun1(A_411,B_412,C_413,D_414) = k7_relat_1(C_413,D_414)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(A_411,B_412)))
      | ~ v1_funct_1(C_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2153,plain,(
    ! [D_414] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_414) = k7_relat_1('#skF_6',D_414)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_2151])).

tff(c_2158,plain,(
    ! [D_414] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_414) = k7_relat_1('#skF_6',D_414) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2153])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_2155,plain,(
    ! [D_414] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_414) = k7_relat_1('#skF_5',D_414)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_2151])).

tff(c_2161,plain,(
    ! [D_414] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_414) = k7_relat_1('#skF_5',D_414) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2155])).

tff(c_136,plain,(
    ! [A_238,B_239,C_240] :
      ( k9_subset_1(A_238,B_239,C_240) = k3_xboole_0(B_239,C_240)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(A_238)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_147,plain,(
    ! [B_239] : k9_subset_1('#skF_1',B_239,'#skF_4') = k3_xboole_0(B_239,'#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_136])).

tff(c_444,plain,(
    ! [A_261,C_262,B_263] :
      ( k9_subset_1(A_261,C_262,B_263) = k9_subset_1(A_261,B_263,C_262)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(A_261)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_450,plain,(
    ! [B_263] : k9_subset_1('#skF_1',B_263,'#skF_4') = k9_subset_1('#skF_1','#skF_4',B_263) ),
    inference(resolution,[status(thm)],[c_56,c_444])).

tff(c_461,plain,(
    ! [B_264] : k9_subset_1('#skF_1','#skF_4',B_264) = k3_xboole_0(B_264,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_450])).

tff(c_148,plain,(
    ! [B_239] : k9_subset_1('#skF_1',B_239,'#skF_3') = k3_xboole_0(B_239,'#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_136])).

tff(c_468,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_148])).

tff(c_127,plain,(
    ! [A_236,B_237] :
      ( r1_xboole_0(A_236,B_237)
      | ~ r1_subset_1(A_236,B_237)
      | v1_xboole_0(B_237)
      | v1_xboole_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_727,plain,(
    ! [A_291,B_292] :
      ( k3_xboole_0(A_291,B_292) = k1_xboole_0
      | ~ r1_subset_1(A_291,B_292)
      | v1_xboole_0(B_292)
      | v1_xboole_0(A_291) ) ),
    inference(resolution,[status(thm)],[c_127,c_2])).

tff(c_730,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_727])).

tff(c_732,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_730])).

tff(c_733,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_732])).

tff(c_93,plain,(
    ! [C_231,A_232,B_233] :
      ( v4_relat_1(C_231,A_232)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_100,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_93])).

tff(c_104,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_14])).

tff(c_107,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_104])).

tff(c_279,plain,(
    ! [C_252,A_253,B_254] :
      ( k7_relat_1(k7_relat_1(C_252,A_253),B_254) = k7_relat_1(C_252,k3_xboole_0(A_253,B_254))
      | ~ v1_relat_1(C_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_315,plain,(
    ! [B_254] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',B_254)) = k7_relat_1('#skF_6',B_254)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_279])).

tff(c_325,plain,(
    ! [B_254] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',B_254)) = k7_relat_1('#skF_6',B_254) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_315])).

tff(c_752,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_733,c_325])).

tff(c_739,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_733,c_468])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_177,plain,(
    ! [C_244,A_245,B_246] :
      ( k7_relat_1(k7_relat_1(C_244,A_245),B_246) = k1_xboole_0
      | ~ r1_xboole_0(A_245,B_246)
      | ~ v1_relat_1(C_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_195,plain,(
    ! [B_246] :
      ( k7_relat_1('#skF_6',B_246) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_246)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_177])).

tff(c_215,plain,(
    ! [B_248] :
      ( k7_relat_1('#skF_6',B_248) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_195])).

tff(c_227,plain,(
    ! [B_2] :
      ( k7_relat_1('#skF_6',B_2) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_215])).

tff(c_10,plain,(
    ! [C_11,A_9,B_10] :
      ( k7_relat_1(k7_relat_1(C_11,A_9),B_10) = k7_relat_1(C_11,k3_xboole_0(A_9,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_804,plain,(
    ! [B_10] :
      ( k7_relat_1(k7_relat_1('#skF_6','#skF_3'),B_10) = k7_relat_1('#skF_6',k3_xboole_0(k1_xboole_0,B_10))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_10])).

tff(c_1044,plain,(
    ! [B_327] : k7_relat_1(k7_relat_1('#skF_6','#skF_3'),B_327) = k7_relat_1('#skF_6',k3_xboole_0(k1_xboole_0,B_327)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_804])).

tff(c_1069,plain,(
    ! [B_327] :
      ( k7_relat_1('#skF_6',k3_xboole_0(k1_xboole_0,B_327)) = k7_relat_1(k1_xboole_0,B_327)
      | k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_1044])).

tff(c_1084,plain,(
    ! [B_327] : k7_relat_1('#skF_6',k3_xboole_0(k1_xboole_0,B_327)) = k7_relat_1(k1_xboole_0,B_327) ),
    inference(demodulation,[status(thm),theory(equality)],[c_733,c_1069])).

tff(c_817,plain,(
    ! [B_10] : k7_relat_1(k7_relat_1('#skF_6','#skF_3'),B_10) = k7_relat_1('#skF_6',k3_xboole_0(k1_xboole_0,B_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_804])).

tff(c_1120,plain,(
    ! [B_330] : k7_relat_1(k7_relat_1('#skF_6','#skF_3'),B_330) = k7_relat_1(k1_xboole_0,B_330) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_817])).

tff(c_1129,plain,(
    ! [B_330] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_330)) = k7_relat_1(k1_xboole_0,B_330)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1120,c_10])).

tff(c_1179,plain,(
    ! [B_337] : k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_337)) = k7_relat_1(k1_xboole_0,B_337) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1129])).

tff(c_1197,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_1179])).

tff(c_1207,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') = k7_relat_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_1197])).

tff(c_12,plain,(
    ! [C_14,A_12,B_13] :
      ( k7_relat_1(k7_relat_1(C_14,A_12),B_13) = k1_xboole_0
      | ~ r1_xboole_0(A_12,B_13)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1135,plain,(
    ! [B_330] :
      ( k7_relat_1(k1_xboole_0,B_330) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_330)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1120,c_12])).

tff(c_1164,plain,(
    ! [B_331] :
      ( k7_relat_1(k1_xboole_0,B_331) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_331) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1135])).

tff(c_1168,plain,(
    ! [B_18] :
      ( k7_relat_1(k1_xboole_0,B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_1164])).

tff(c_1233,plain,(
    ! [B_338] :
      ( k7_relat_1(k1_xboole_0,B_338) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_338)
      | v1_xboole_0(B_338) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1168])).

tff(c_1236,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1233])).

tff(c_1238,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1207,c_1236])).

tff(c_1239,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1238])).

tff(c_1242,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1239,c_752])).

tff(c_589,plain,(
    ! [A_268,B_269,C_270,D_271] :
      ( k2_partfun1(A_268,B_269,C_270,D_271) = k7_relat_1(C_270,D_271)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_268,B_269)))
      | ~ v1_funct_1(C_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_591,plain,(
    ! [D_271] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_271) = k7_relat_1('#skF_6',D_271)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_589])).

tff(c_596,plain,(
    ! [D_271] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_271) = k7_relat_1('#skF_6',D_271) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_591])).

tff(c_101,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_93])).

tff(c_115,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_101,c_14])).

tff(c_118,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_115])).

tff(c_192,plain,(
    ! [B_246] :
      ( k7_relat_1('#skF_5',B_246) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_246)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_177])).

tff(c_202,plain,(
    ! [B_247] :
      ( k7_relat_1('#skF_5',B_247) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_192])).

tff(c_206,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_5',B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_202])).

tff(c_377,plain,(
    ! [B_258] :
      ( k7_relat_1('#skF_5',B_258) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_258)
      | v1_xboole_0(B_258) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_206])).

tff(c_380,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_377])).

tff(c_383,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_380])).

tff(c_312,plain,(
    ! [B_254] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',B_254)) = k7_relat_1('#skF_5',B_254)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_279])).

tff(c_323,plain,(
    ! [B_254] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',B_254)) = k7_relat_1('#skF_5',B_254) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_312])).

tff(c_491,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')) = k7_relat_1('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_323])).

tff(c_494,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_491])).

tff(c_738,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_733,c_494])).

tff(c_593,plain,(
    ! [D_271] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_271) = k7_relat_1('#skF_5',D_271)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_589])).

tff(c_599,plain,(
    ! [D_271] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_271) = k7_relat_1('#skF_5',D_271) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_593])).

tff(c_40,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_83,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_149,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_147,c_83])).

tff(c_1726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_596,c_738,c_599,c_739,c_739,c_149])).

tff(c_1728,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1798,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1796,c_1796,c_1728])).

tff(c_51013,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2027,c_1910,c_2112,c_2025,c_2158,c_2161,c_1798])).

tff(c_1771,plain,(
    ! [A_380,B_381] :
      ( r1_xboole_0(A_380,B_381)
      | ~ r1_subset_1(A_380,B_381)
      | v1_xboole_0(B_381)
      | v1_xboole_0(A_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_51172,plain,(
    ! [A_1734,B_1735] :
      ( k3_xboole_0(A_1734,B_1735) = k1_xboole_0
      | ~ r1_subset_1(A_1734,B_1735)
      | v1_xboole_0(B_1735)
      | v1_xboole_0(A_1734) ) ),
    inference(resolution,[status(thm)],[c_1771,c_2])).

tff(c_51175,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_51172])).

tff(c_51177,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1910,c_51175])).

tff(c_51178,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_51177])).

tff(c_51196,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_51178,c_2027])).

tff(c_51202,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_51013,c_51196])).

tff(c_1894,plain,(
    ! [B_398] : k9_subset_1('#skF_1',B_398,'#skF_3') = k9_subset_1('#skF_1','#skF_3',B_398) ),
    inference(resolution,[status(thm)],[c_60,c_1886])).

tff(c_1902,plain,(
    ! [B_398] : k9_subset_1('#skF_1','#skF_3',B_398) = k3_xboole_0(B_398,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1797,c_1894])).

tff(c_2028,plain,(
    ! [B_406] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',B_406)) = k7_relat_1('#skF_5',B_406) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2016])).

tff(c_2049,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')) = k7_relat_1('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1910,c_2028])).

tff(c_2180,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2112,c_2049])).

tff(c_51182,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_51178,c_2180])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_44,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_51204,plain,(
    ! [B_1739,D_1740,A_1741,F_1736,C_1738,E_1737] :
      ( v1_funct_1(k1_tmap_1(A_1741,B_1739,C_1738,D_1740,E_1737,F_1736))
      | ~ m1_subset_1(F_1736,k1_zfmisc_1(k2_zfmisc_1(D_1740,B_1739)))
      | ~ v1_funct_2(F_1736,D_1740,B_1739)
      | ~ v1_funct_1(F_1736)
      | ~ m1_subset_1(E_1737,k1_zfmisc_1(k2_zfmisc_1(C_1738,B_1739)))
      | ~ v1_funct_2(E_1737,C_1738,B_1739)
      | ~ v1_funct_1(E_1737)
      | ~ m1_subset_1(D_1740,k1_zfmisc_1(A_1741))
      | v1_xboole_0(D_1740)
      | ~ m1_subset_1(C_1738,k1_zfmisc_1(A_1741))
      | v1_xboole_0(C_1738)
      | v1_xboole_0(B_1739)
      | v1_xboole_0(A_1741) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_51206,plain,(
    ! [A_1741,C_1738,E_1737] :
      ( v1_funct_1(k1_tmap_1(A_1741,'#skF_2',C_1738,'#skF_4',E_1737,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1737,k1_zfmisc_1(k2_zfmisc_1(C_1738,'#skF_2')))
      | ~ v1_funct_2(E_1737,C_1738,'#skF_2')
      | ~ v1_funct_1(E_1737)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1741))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1738,k1_zfmisc_1(A_1741))
      | v1_xboole_0(C_1738)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1741) ) ),
    inference(resolution,[status(thm)],[c_42,c_51204])).

tff(c_51211,plain,(
    ! [A_1741,C_1738,E_1737] :
      ( v1_funct_1(k1_tmap_1(A_1741,'#skF_2',C_1738,'#skF_4',E_1737,'#skF_6'))
      | ~ m1_subset_1(E_1737,k1_zfmisc_1(k2_zfmisc_1(C_1738,'#skF_2')))
      | ~ v1_funct_2(E_1737,C_1738,'#skF_2')
      | ~ v1_funct_1(E_1737)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1741))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1738,k1_zfmisc_1(A_1741))
      | v1_xboole_0(C_1738)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1741) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_51206])).

tff(c_51562,plain,(
    ! [A_1785,C_1786,E_1787] :
      ( v1_funct_1(k1_tmap_1(A_1785,'#skF_2',C_1786,'#skF_4',E_1787,'#skF_6'))
      | ~ m1_subset_1(E_1787,k1_zfmisc_1(k2_zfmisc_1(C_1786,'#skF_2')))
      | ~ v1_funct_2(E_1787,C_1786,'#skF_2')
      | ~ v1_funct_1(E_1787)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1785))
      | ~ m1_subset_1(C_1786,k1_zfmisc_1(A_1785))
      | v1_xboole_0(C_1786)
      | v1_xboole_0(A_1785) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_51211])).

tff(c_51569,plain,(
    ! [A_1785] :
      ( v1_funct_1(k1_tmap_1(A_1785,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1785))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1785))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1785) ) ),
    inference(resolution,[status(thm)],[c_48,c_51562])).

tff(c_51579,plain,(
    ! [A_1785] :
      ( v1_funct_1(k1_tmap_1(A_1785,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1785))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1785))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1785) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_51569])).

tff(c_52024,plain,(
    ! [A_1820] :
      ( v1_funct_1(k1_tmap_1(A_1820,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1820))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1820))
      | v1_xboole_0(A_1820) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_51579])).

tff(c_52027,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_52024])).

tff(c_52030,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52027])).

tff(c_52031,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_52030])).

tff(c_36,plain,(
    ! [C_158,A_156,D_159,B_157,F_161,E_160] :
      ( v1_funct_2(k1_tmap_1(A_156,B_157,C_158,D_159,E_160,F_161),k4_subset_1(A_156,C_158,D_159),B_157)
      | ~ m1_subset_1(F_161,k1_zfmisc_1(k2_zfmisc_1(D_159,B_157)))
      | ~ v1_funct_2(F_161,D_159,B_157)
      | ~ v1_funct_1(F_161)
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(C_158,B_157)))
      | ~ v1_funct_2(E_160,C_158,B_157)
      | ~ v1_funct_1(E_160)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(A_156))
      | v1_xboole_0(D_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(A_156))
      | v1_xboole_0(C_158)
      | v1_xboole_0(B_157)
      | v1_xboole_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_34,plain,(
    ! [C_158,A_156,D_159,B_157,F_161,E_160] :
      ( m1_subset_1(k1_tmap_1(A_156,B_157,C_158,D_159,E_160,F_161),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_156,C_158,D_159),B_157)))
      | ~ m1_subset_1(F_161,k1_zfmisc_1(k2_zfmisc_1(D_159,B_157)))
      | ~ v1_funct_2(F_161,D_159,B_157)
      | ~ v1_funct_1(F_161)
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(C_158,B_157)))
      | ~ v1_funct_2(E_160,C_158,B_157)
      | ~ v1_funct_1(E_160)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(A_156))
      | v1_xboole_0(D_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(A_156))
      | v1_xboole_0(C_158)
      | v1_xboole_0(B_157)
      | v1_xboole_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_51626,plain,(
    ! [D_1794,C_1792,F_1793,E_1796,B_1797,A_1795] :
      ( k2_partfun1(k4_subset_1(A_1795,C_1792,D_1794),B_1797,k1_tmap_1(A_1795,B_1797,C_1792,D_1794,E_1796,F_1793),C_1792) = E_1796
      | ~ m1_subset_1(k1_tmap_1(A_1795,B_1797,C_1792,D_1794,E_1796,F_1793),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1795,C_1792,D_1794),B_1797)))
      | ~ v1_funct_2(k1_tmap_1(A_1795,B_1797,C_1792,D_1794,E_1796,F_1793),k4_subset_1(A_1795,C_1792,D_1794),B_1797)
      | ~ v1_funct_1(k1_tmap_1(A_1795,B_1797,C_1792,D_1794,E_1796,F_1793))
      | k2_partfun1(D_1794,B_1797,F_1793,k9_subset_1(A_1795,C_1792,D_1794)) != k2_partfun1(C_1792,B_1797,E_1796,k9_subset_1(A_1795,C_1792,D_1794))
      | ~ m1_subset_1(F_1793,k1_zfmisc_1(k2_zfmisc_1(D_1794,B_1797)))
      | ~ v1_funct_2(F_1793,D_1794,B_1797)
      | ~ v1_funct_1(F_1793)
      | ~ m1_subset_1(E_1796,k1_zfmisc_1(k2_zfmisc_1(C_1792,B_1797)))
      | ~ v1_funct_2(E_1796,C_1792,B_1797)
      | ~ v1_funct_1(E_1796)
      | ~ m1_subset_1(D_1794,k1_zfmisc_1(A_1795))
      | v1_xboole_0(D_1794)
      | ~ m1_subset_1(C_1792,k1_zfmisc_1(A_1795))
      | v1_xboole_0(C_1792)
      | v1_xboole_0(B_1797)
      | v1_xboole_0(A_1795) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_116122,plain,(
    ! [E_3252,B_3254,A_3256,D_3255,C_3253,F_3251] :
      ( k2_partfun1(k4_subset_1(A_3256,C_3253,D_3255),B_3254,k1_tmap_1(A_3256,B_3254,C_3253,D_3255,E_3252,F_3251),C_3253) = E_3252
      | ~ v1_funct_2(k1_tmap_1(A_3256,B_3254,C_3253,D_3255,E_3252,F_3251),k4_subset_1(A_3256,C_3253,D_3255),B_3254)
      | ~ v1_funct_1(k1_tmap_1(A_3256,B_3254,C_3253,D_3255,E_3252,F_3251))
      | k2_partfun1(D_3255,B_3254,F_3251,k9_subset_1(A_3256,C_3253,D_3255)) != k2_partfun1(C_3253,B_3254,E_3252,k9_subset_1(A_3256,C_3253,D_3255))
      | ~ m1_subset_1(F_3251,k1_zfmisc_1(k2_zfmisc_1(D_3255,B_3254)))
      | ~ v1_funct_2(F_3251,D_3255,B_3254)
      | ~ v1_funct_1(F_3251)
      | ~ m1_subset_1(E_3252,k1_zfmisc_1(k2_zfmisc_1(C_3253,B_3254)))
      | ~ v1_funct_2(E_3252,C_3253,B_3254)
      | ~ v1_funct_1(E_3252)
      | ~ m1_subset_1(D_3255,k1_zfmisc_1(A_3256))
      | v1_xboole_0(D_3255)
      | ~ m1_subset_1(C_3253,k1_zfmisc_1(A_3256))
      | v1_xboole_0(C_3253)
      | v1_xboole_0(B_3254)
      | v1_xboole_0(A_3256) ) ),
    inference(resolution,[status(thm)],[c_34,c_51626])).

tff(c_145582,plain,(
    ! [C_3932,D_3934,B_3933,F_3930,A_3935,E_3931] :
      ( k2_partfun1(k4_subset_1(A_3935,C_3932,D_3934),B_3933,k1_tmap_1(A_3935,B_3933,C_3932,D_3934,E_3931,F_3930),C_3932) = E_3931
      | ~ v1_funct_1(k1_tmap_1(A_3935,B_3933,C_3932,D_3934,E_3931,F_3930))
      | k2_partfun1(D_3934,B_3933,F_3930,k9_subset_1(A_3935,C_3932,D_3934)) != k2_partfun1(C_3932,B_3933,E_3931,k9_subset_1(A_3935,C_3932,D_3934))
      | ~ m1_subset_1(F_3930,k1_zfmisc_1(k2_zfmisc_1(D_3934,B_3933)))
      | ~ v1_funct_2(F_3930,D_3934,B_3933)
      | ~ v1_funct_1(F_3930)
      | ~ m1_subset_1(E_3931,k1_zfmisc_1(k2_zfmisc_1(C_3932,B_3933)))
      | ~ v1_funct_2(E_3931,C_3932,B_3933)
      | ~ v1_funct_1(E_3931)
      | ~ m1_subset_1(D_3934,k1_zfmisc_1(A_3935))
      | v1_xboole_0(D_3934)
      | ~ m1_subset_1(C_3932,k1_zfmisc_1(A_3935))
      | v1_xboole_0(C_3932)
      | v1_xboole_0(B_3933)
      | v1_xboole_0(A_3935) ) ),
    inference(resolution,[status(thm)],[c_36,c_116122])).

tff(c_145586,plain,(
    ! [A_3935,C_3932,E_3931] :
      ( k2_partfun1(k4_subset_1(A_3935,C_3932,'#skF_4'),'#skF_2',k1_tmap_1(A_3935,'#skF_2',C_3932,'#skF_4',E_3931,'#skF_6'),C_3932) = E_3931
      | ~ v1_funct_1(k1_tmap_1(A_3935,'#skF_2',C_3932,'#skF_4',E_3931,'#skF_6'))
      | k2_partfun1(C_3932,'#skF_2',E_3931,k9_subset_1(A_3935,C_3932,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_3935,C_3932,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_3931,k1_zfmisc_1(k2_zfmisc_1(C_3932,'#skF_2')))
      | ~ v1_funct_2(E_3931,C_3932,'#skF_2')
      | ~ v1_funct_1(E_3931)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3935))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3932,k1_zfmisc_1(A_3935))
      | v1_xboole_0(C_3932)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3935) ) ),
    inference(resolution,[status(thm)],[c_42,c_145582])).

tff(c_145592,plain,(
    ! [A_3935,C_3932,E_3931] :
      ( k2_partfun1(k4_subset_1(A_3935,C_3932,'#skF_4'),'#skF_2',k1_tmap_1(A_3935,'#skF_2',C_3932,'#skF_4',E_3931,'#skF_6'),C_3932) = E_3931
      | ~ v1_funct_1(k1_tmap_1(A_3935,'#skF_2',C_3932,'#skF_4',E_3931,'#skF_6'))
      | k2_partfun1(C_3932,'#skF_2',E_3931,k9_subset_1(A_3935,C_3932,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3935,C_3932,'#skF_4'))
      | ~ m1_subset_1(E_3931,k1_zfmisc_1(k2_zfmisc_1(C_3932,'#skF_2')))
      | ~ v1_funct_2(E_3931,C_3932,'#skF_2')
      | ~ v1_funct_1(E_3931)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3935))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3932,k1_zfmisc_1(A_3935))
      | v1_xboole_0(C_3932)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3935) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2158,c_145586])).

tff(c_155709,plain,(
    ! [A_4189,C_4190,E_4191] :
      ( k2_partfun1(k4_subset_1(A_4189,C_4190,'#skF_4'),'#skF_2',k1_tmap_1(A_4189,'#skF_2',C_4190,'#skF_4',E_4191,'#skF_6'),C_4190) = E_4191
      | ~ v1_funct_1(k1_tmap_1(A_4189,'#skF_2',C_4190,'#skF_4',E_4191,'#skF_6'))
      | k2_partfun1(C_4190,'#skF_2',E_4191,k9_subset_1(A_4189,C_4190,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4189,C_4190,'#skF_4'))
      | ~ m1_subset_1(E_4191,k1_zfmisc_1(k2_zfmisc_1(C_4190,'#skF_2')))
      | ~ v1_funct_2(E_4191,C_4190,'#skF_2')
      | ~ v1_funct_1(E_4191)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4189))
      | ~ m1_subset_1(C_4190,k1_zfmisc_1(A_4189))
      | v1_xboole_0(C_4190)
      | v1_xboole_0(A_4189) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_145592])).

tff(c_155716,plain,(
    ! [A_4189] :
      ( k2_partfun1(k4_subset_1(A_4189,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_4189,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_4189,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_4189,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4189,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4189))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4189))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4189) ) ),
    inference(resolution,[status(thm)],[c_48,c_155709])).

tff(c_155726,plain,(
    ! [A_4189] :
      ( k2_partfun1(k4_subset_1(A_4189,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_4189,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_4189,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_4189,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4189,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4189))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4189))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2161,c_155716])).

tff(c_159426,plain,(
    ! [A_4219] :
      ( k2_partfun1(k4_subset_1(A_4219,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_4219,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_4219,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_4219,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4219,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4219))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4219))
      | v1_xboole_0(A_4219) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_155726])).

tff(c_2320,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2180,c_2161,c_2027,c_2158,c_1910,c_1910,c_1798])).

tff(c_2511,plain,(
    ! [A_442,B_443] :
      ( k3_xboole_0(A_442,B_443) = k1_xboole_0
      | ~ r1_subset_1(A_442,B_443)
      | v1_xboole_0(B_443)
      | v1_xboole_0(A_442) ) ),
    inference(resolution,[status(thm)],[c_1771,c_2])).

tff(c_2514,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2511])).

tff(c_2516,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1910,c_2514])).

tff(c_2517,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_2516])).

tff(c_2535,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2517,c_2027])).

tff(c_2541,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2320,c_2535])).

tff(c_2521,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2517,c_2180])).

tff(c_2484,plain,(
    ! [D_436,B_435,A_437,E_433,F_432,C_434] :
      ( v1_funct_1(k1_tmap_1(A_437,B_435,C_434,D_436,E_433,F_432))
      | ~ m1_subset_1(F_432,k1_zfmisc_1(k2_zfmisc_1(D_436,B_435)))
      | ~ v1_funct_2(F_432,D_436,B_435)
      | ~ v1_funct_1(F_432)
      | ~ m1_subset_1(E_433,k1_zfmisc_1(k2_zfmisc_1(C_434,B_435)))
      | ~ v1_funct_2(E_433,C_434,B_435)
      | ~ v1_funct_1(E_433)
      | ~ m1_subset_1(D_436,k1_zfmisc_1(A_437))
      | v1_xboole_0(D_436)
      | ~ m1_subset_1(C_434,k1_zfmisc_1(A_437))
      | v1_xboole_0(C_434)
      | v1_xboole_0(B_435)
      | v1_xboole_0(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_2486,plain,(
    ! [A_437,C_434,E_433] :
      ( v1_funct_1(k1_tmap_1(A_437,'#skF_2',C_434,'#skF_4',E_433,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_433,k1_zfmisc_1(k2_zfmisc_1(C_434,'#skF_2')))
      | ~ v1_funct_2(E_433,C_434,'#skF_2')
      | ~ v1_funct_1(E_433)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_437))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_434,k1_zfmisc_1(A_437))
      | v1_xboole_0(C_434)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_437) ) ),
    inference(resolution,[status(thm)],[c_42,c_2484])).

tff(c_2491,plain,(
    ! [A_437,C_434,E_433] :
      ( v1_funct_1(k1_tmap_1(A_437,'#skF_2',C_434,'#skF_4',E_433,'#skF_6'))
      | ~ m1_subset_1(E_433,k1_zfmisc_1(k2_zfmisc_1(C_434,'#skF_2')))
      | ~ v1_funct_2(E_433,C_434,'#skF_2')
      | ~ v1_funct_1(E_433)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_437))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_434,k1_zfmisc_1(A_437))
      | v1_xboole_0(C_434)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_437) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2486])).

tff(c_2816,plain,(
    ! [A_474,C_475,E_476] :
      ( v1_funct_1(k1_tmap_1(A_474,'#skF_2',C_475,'#skF_4',E_476,'#skF_6'))
      | ~ m1_subset_1(E_476,k1_zfmisc_1(k2_zfmisc_1(C_475,'#skF_2')))
      | ~ v1_funct_2(E_476,C_475,'#skF_2')
      | ~ v1_funct_1(E_476)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_474))
      | ~ m1_subset_1(C_475,k1_zfmisc_1(A_474))
      | v1_xboole_0(C_475)
      | v1_xboole_0(A_474) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_2491])).

tff(c_2823,plain,(
    ! [A_474] :
      ( v1_funct_1(k1_tmap_1(A_474,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_474))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_474))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_474) ) ),
    inference(resolution,[status(thm)],[c_48,c_2816])).

tff(c_2833,plain,(
    ! [A_474] :
      ( v1_funct_1(k1_tmap_1(A_474,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_474))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_474))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_474) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2823])).

tff(c_3116,plain,(
    ! [A_511] :
      ( v1_funct_1(k1_tmap_1(A_511,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_511))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_511))
      | v1_xboole_0(A_511) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2833])).

tff(c_3119,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_3116])).

tff(c_3122,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3119])).

tff(c_3123,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3122])).

tff(c_2884,plain,(
    ! [F_486,D_487,A_488,B_490,E_489,C_485] :
      ( k2_partfun1(k4_subset_1(A_488,C_485,D_487),B_490,k1_tmap_1(A_488,B_490,C_485,D_487,E_489,F_486),D_487) = F_486
      | ~ m1_subset_1(k1_tmap_1(A_488,B_490,C_485,D_487,E_489,F_486),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_488,C_485,D_487),B_490)))
      | ~ v1_funct_2(k1_tmap_1(A_488,B_490,C_485,D_487,E_489,F_486),k4_subset_1(A_488,C_485,D_487),B_490)
      | ~ v1_funct_1(k1_tmap_1(A_488,B_490,C_485,D_487,E_489,F_486))
      | k2_partfun1(D_487,B_490,F_486,k9_subset_1(A_488,C_485,D_487)) != k2_partfun1(C_485,B_490,E_489,k9_subset_1(A_488,C_485,D_487))
      | ~ m1_subset_1(F_486,k1_zfmisc_1(k2_zfmisc_1(D_487,B_490)))
      | ~ v1_funct_2(F_486,D_487,B_490)
      | ~ v1_funct_1(F_486)
      | ~ m1_subset_1(E_489,k1_zfmisc_1(k2_zfmisc_1(C_485,B_490)))
      | ~ v1_funct_2(E_489,C_485,B_490)
      | ~ v1_funct_1(E_489)
      | ~ m1_subset_1(D_487,k1_zfmisc_1(A_488))
      | v1_xboole_0(D_487)
      | ~ m1_subset_1(C_485,k1_zfmisc_1(A_488))
      | v1_xboole_0(C_485)
      | v1_xboole_0(B_490)
      | v1_xboole_0(A_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_7446,plain,(
    ! [A_715,B_713,F_710,C_712,D_714,E_711] :
      ( k2_partfun1(k4_subset_1(A_715,C_712,D_714),B_713,k1_tmap_1(A_715,B_713,C_712,D_714,E_711,F_710),D_714) = F_710
      | ~ v1_funct_2(k1_tmap_1(A_715,B_713,C_712,D_714,E_711,F_710),k4_subset_1(A_715,C_712,D_714),B_713)
      | ~ v1_funct_1(k1_tmap_1(A_715,B_713,C_712,D_714,E_711,F_710))
      | k2_partfun1(D_714,B_713,F_710,k9_subset_1(A_715,C_712,D_714)) != k2_partfun1(C_712,B_713,E_711,k9_subset_1(A_715,C_712,D_714))
      | ~ m1_subset_1(F_710,k1_zfmisc_1(k2_zfmisc_1(D_714,B_713)))
      | ~ v1_funct_2(F_710,D_714,B_713)
      | ~ v1_funct_1(F_710)
      | ~ m1_subset_1(E_711,k1_zfmisc_1(k2_zfmisc_1(C_712,B_713)))
      | ~ v1_funct_2(E_711,C_712,B_713)
      | ~ v1_funct_1(E_711)
      | ~ m1_subset_1(D_714,k1_zfmisc_1(A_715))
      | v1_xboole_0(D_714)
      | ~ m1_subset_1(C_712,k1_zfmisc_1(A_715))
      | v1_xboole_0(C_712)
      | v1_xboole_0(B_713)
      | v1_xboole_0(A_715) ) ),
    inference(resolution,[status(thm)],[c_34,c_2884])).

tff(c_36570,plain,(
    ! [B_1414,E_1412,C_1413,F_1411,A_1416,D_1415] :
      ( k2_partfun1(k4_subset_1(A_1416,C_1413,D_1415),B_1414,k1_tmap_1(A_1416,B_1414,C_1413,D_1415,E_1412,F_1411),D_1415) = F_1411
      | ~ v1_funct_1(k1_tmap_1(A_1416,B_1414,C_1413,D_1415,E_1412,F_1411))
      | k2_partfun1(D_1415,B_1414,F_1411,k9_subset_1(A_1416,C_1413,D_1415)) != k2_partfun1(C_1413,B_1414,E_1412,k9_subset_1(A_1416,C_1413,D_1415))
      | ~ m1_subset_1(F_1411,k1_zfmisc_1(k2_zfmisc_1(D_1415,B_1414)))
      | ~ v1_funct_2(F_1411,D_1415,B_1414)
      | ~ v1_funct_1(F_1411)
      | ~ m1_subset_1(E_1412,k1_zfmisc_1(k2_zfmisc_1(C_1413,B_1414)))
      | ~ v1_funct_2(E_1412,C_1413,B_1414)
      | ~ v1_funct_1(E_1412)
      | ~ m1_subset_1(D_1415,k1_zfmisc_1(A_1416))
      | v1_xboole_0(D_1415)
      | ~ m1_subset_1(C_1413,k1_zfmisc_1(A_1416))
      | v1_xboole_0(C_1413)
      | v1_xboole_0(B_1414)
      | v1_xboole_0(A_1416) ) ),
    inference(resolution,[status(thm)],[c_36,c_7446])).

tff(c_36574,plain,(
    ! [A_1416,C_1413,E_1412] :
      ( k2_partfun1(k4_subset_1(A_1416,C_1413,'#skF_4'),'#skF_2',k1_tmap_1(A_1416,'#skF_2',C_1413,'#skF_4',E_1412,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1416,'#skF_2',C_1413,'#skF_4',E_1412,'#skF_6'))
      | k2_partfun1(C_1413,'#skF_2',E_1412,k9_subset_1(A_1416,C_1413,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1416,C_1413,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1412,k1_zfmisc_1(k2_zfmisc_1(C_1413,'#skF_2')))
      | ~ v1_funct_2(E_1412,C_1413,'#skF_2')
      | ~ v1_funct_1(E_1412)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1416))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1413,k1_zfmisc_1(A_1416))
      | v1_xboole_0(C_1413)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1416) ) ),
    inference(resolution,[status(thm)],[c_42,c_36570])).

tff(c_36580,plain,(
    ! [A_1416,C_1413,E_1412] :
      ( k2_partfun1(k4_subset_1(A_1416,C_1413,'#skF_4'),'#skF_2',k1_tmap_1(A_1416,'#skF_2',C_1413,'#skF_4',E_1412,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1416,'#skF_2',C_1413,'#skF_4',E_1412,'#skF_6'))
      | k2_partfun1(C_1413,'#skF_2',E_1412,k9_subset_1(A_1416,C_1413,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1416,C_1413,'#skF_4'))
      | ~ m1_subset_1(E_1412,k1_zfmisc_1(k2_zfmisc_1(C_1413,'#skF_2')))
      | ~ v1_funct_2(E_1412,C_1413,'#skF_2')
      | ~ v1_funct_1(E_1412)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1416))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1413,k1_zfmisc_1(A_1416))
      | v1_xboole_0(C_1413)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1416) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2158,c_36574])).

tff(c_48586,plain,(
    ! [A_1669,C_1670,E_1671] :
      ( k2_partfun1(k4_subset_1(A_1669,C_1670,'#skF_4'),'#skF_2',k1_tmap_1(A_1669,'#skF_2',C_1670,'#skF_4',E_1671,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1669,'#skF_2',C_1670,'#skF_4',E_1671,'#skF_6'))
      | k2_partfun1(C_1670,'#skF_2',E_1671,k9_subset_1(A_1669,C_1670,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1669,C_1670,'#skF_4'))
      | ~ m1_subset_1(E_1671,k1_zfmisc_1(k2_zfmisc_1(C_1670,'#skF_2')))
      | ~ v1_funct_2(E_1671,C_1670,'#skF_2')
      | ~ v1_funct_1(E_1671)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1669))
      | ~ m1_subset_1(C_1670,k1_zfmisc_1(A_1669))
      | v1_xboole_0(C_1670)
      | v1_xboole_0(A_1669) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_36580])).

tff(c_48593,plain,(
    ! [A_1669] :
      ( k2_partfun1(k4_subset_1(A_1669,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1669,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1669,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1669,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1669,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1669))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1669))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1669) ) ),
    inference(resolution,[status(thm)],[c_48,c_48586])).

tff(c_48603,plain,(
    ! [A_1669] :
      ( k2_partfun1(k4_subset_1(A_1669,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1669,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1669,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1669,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1669,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1669))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1669))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1669) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2161,c_48593])).

tff(c_50942,plain,(
    ! [A_1721] :
      ( k2_partfun1(k4_subset_1(A_1721,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1721,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1721,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1721,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1721,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1721))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1721))
      | v1_xboole_0(A_1721) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_48603])).

tff(c_1727,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2288,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1727])).

tff(c_50953,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_50942,c_2288])).

tff(c_50967,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_2541,c_2517,c_1902,c_2521,c_2517,c_1902,c_3123,c_50953])).

tff(c_50969,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_50967])).

tff(c_50970,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1727])).

tff(c_159438,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_159426,c_50970])).

tff(c_159452,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_51202,c_51178,c_1902,c_51182,c_51178,c_1902,c_52031,c_159438])).

tff(c_159454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_159452])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 48.56/36.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.56/36.93  
% 48.56/36.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.56/36.93  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 48.56/36.93  
% 48.56/36.93  %Foreground sorts:
% 48.56/36.93  
% 48.56/36.93  
% 48.56/36.93  %Background operators:
% 48.56/36.93  
% 48.56/36.93  
% 48.56/36.93  %Foreground operators:
% 48.56/36.93  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 48.56/36.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 48.56/36.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 48.56/36.93  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 48.56/36.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 48.56/36.93  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 48.56/36.93  tff('#skF_5', type, '#skF_5': $i).
% 48.56/36.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 48.56/36.93  tff('#skF_6', type, '#skF_6': $i).
% 48.56/36.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 48.56/36.93  tff('#skF_2', type, '#skF_2': $i).
% 48.56/36.93  tff('#skF_3', type, '#skF_3': $i).
% 48.56/36.93  tff('#skF_1', type, '#skF_1': $i).
% 48.56/36.93  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 48.56/36.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 48.56/36.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 48.56/36.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 48.56/36.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 48.56/36.93  tff('#skF_4', type, '#skF_4': $i).
% 48.56/36.93  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 48.56/36.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 48.56/36.93  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 48.56/36.93  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 48.56/36.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 48.56/36.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 48.56/36.93  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 48.56/36.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 48.56/36.93  
% 48.75/36.96  tff(f_203, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 48.75/36.96  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 48.75/36.96  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 48.75/36.96  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 48.75/36.96  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 48.75/36.96  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 48.75/36.96  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 48.75/36.96  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 48.75/36.96  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 48.75/36.96  tff(f_79, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 48.75/36.96  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 48.75/36.96  tff(f_161, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 48.75/36.96  tff(f_127, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 48.75/36.96  tff(c_66, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 48.75/36.96  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 48.75/36.96  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 48.75/36.96  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_203])).
% 48.75/36.96  tff(c_73, plain, (![C_223, A_224, B_225]: (v1_relat_1(C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 48.75/36.96  tff(c_80, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_73])).
% 48.75/36.96  tff(c_1742, plain, (![C_377, A_378, B_379]: (v4_relat_1(C_377, A_378) | ~m1_subset_1(C_377, k1_zfmisc_1(k2_zfmisc_1(A_378, B_379))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 48.75/36.96  tff(c_1749, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_1742])).
% 48.75/36.96  tff(c_14, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)=B_16 | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 48.75/36.96  tff(c_1753, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1749, c_14])).
% 48.75/36.96  tff(c_1756, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1753])).
% 48.75/36.96  tff(c_1986, plain, (![C_403, A_404, B_405]: (k7_relat_1(k7_relat_1(C_403, A_404), B_405)=k7_relat_1(C_403, k3_xboole_0(A_404, B_405)) | ~v1_relat_1(C_403))), inference(cnfTransformation, [status(thm)], [f_41])).
% 48.75/36.96  tff(c_2019, plain, (![B_405]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', B_405))=k7_relat_1('#skF_6', B_405) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1756, c_1986])).
% 48.75/36.96  tff(c_2027, plain, (![B_405]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', B_405))=k7_relat_1('#skF_6', B_405))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2019])).
% 48.75/36.96  tff(c_1785, plain, (![A_384, B_385, C_386]: (k9_subset_1(A_384, B_385, C_386)=k3_xboole_0(B_385, C_386) | ~m1_subset_1(C_386, k1_zfmisc_1(A_384)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 48.75/36.96  tff(c_1796, plain, (![B_385]: (k9_subset_1('#skF_1', B_385, '#skF_4')=k3_xboole_0(B_385, '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_1785])).
% 48.75/36.96  tff(c_1886, plain, (![A_396, C_397, B_398]: (k9_subset_1(A_396, C_397, B_398)=k9_subset_1(A_396, B_398, C_397) | ~m1_subset_1(C_397, k1_zfmisc_1(A_396)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 48.75/36.96  tff(c_1892, plain, (![B_398]: (k9_subset_1('#skF_1', B_398, '#skF_4')=k9_subset_1('#skF_1', '#skF_4', B_398))), inference(resolution, [status(thm)], [c_56, c_1886])).
% 48.75/36.96  tff(c_1903, plain, (![B_399]: (k9_subset_1('#skF_1', '#skF_4', B_399)=k3_xboole_0(B_399, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1796, c_1892])).
% 48.75/36.96  tff(c_1797, plain, (![B_385]: (k9_subset_1('#skF_1', B_385, '#skF_3')=k3_xboole_0(B_385, '#skF_3'))), inference(resolution, [status(thm)], [c_60, c_1785])).
% 48.75/36.96  tff(c_1910, plain, (k3_xboole_0('#skF_3', '#skF_4')=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1903, c_1797])).
% 48.75/36.96  tff(c_58, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_203])).
% 48.75/36.96  tff(c_54, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_203])).
% 48.75/36.96  tff(c_62, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 48.75/36.96  tff(c_18, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | ~r1_subset_1(A_17, B_18) | v1_xboole_0(B_18) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 48.75/36.96  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_203])).
% 48.75/36.96  tff(c_81, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_73])).
% 48.75/36.96  tff(c_1750, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_1742])).
% 48.75/36.96  tff(c_1759, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1750, c_14])).
% 48.75/36.96  tff(c_1762, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1759])).
% 48.75/36.96  tff(c_1835, plain, (![C_391, A_392, B_393]: (k7_relat_1(k7_relat_1(C_391, A_392), B_393)=k1_xboole_0 | ~r1_xboole_0(A_392, B_393) | ~v1_relat_1(C_391))), inference(cnfTransformation, [status(thm)], [f_47])).
% 48.75/36.96  tff(c_1850, plain, (![B_393]: (k7_relat_1('#skF_5', B_393)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_393) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1762, c_1835])).
% 48.75/36.96  tff(c_1860, plain, (![B_394]: (k7_relat_1('#skF_5', B_394)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_394))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1850])).
% 48.75/36.96  tff(c_1864, plain, (![B_18]: (k7_relat_1('#skF_5', B_18)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_1860])).
% 48.75/36.96  tff(c_2106, plain, (![B_409]: (k7_relat_1('#skF_5', B_409)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_409) | v1_xboole_0(B_409))), inference(negUnitSimplification, [status(thm)], [c_62, c_1864])).
% 48.75/36.96  tff(c_2109, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_2106])).
% 48.75/36.96  tff(c_2112, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_2109])).
% 48.75/36.96  tff(c_2016, plain, (![B_405]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', B_405))=k7_relat_1('#skF_5', B_405) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1762, c_1986])).
% 48.75/36.96  tff(c_2025, plain, (![B_405]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', B_405))=k7_relat_1('#skF_5', B_405))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_2016])).
% 48.75/36.96  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_203])).
% 48.75/36.96  tff(c_2151, plain, (![A_411, B_412, C_413, D_414]: (k2_partfun1(A_411, B_412, C_413, D_414)=k7_relat_1(C_413, D_414) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(A_411, B_412))) | ~v1_funct_1(C_413))), inference(cnfTransformation, [status(thm)], [f_79])).
% 48.75/36.96  tff(c_2153, plain, (![D_414]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_414)=k7_relat_1('#skF_6', D_414) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_42, c_2151])).
% 48.75/36.96  tff(c_2158, plain, (![D_414]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_414)=k7_relat_1('#skF_6', D_414))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2153])).
% 48.75/36.96  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_203])).
% 48.75/36.96  tff(c_2155, plain, (![D_414]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_414)=k7_relat_1('#skF_5', D_414) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_2151])).
% 48.75/36.96  tff(c_2161, plain, (![D_414]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_414)=k7_relat_1('#skF_5', D_414))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2155])).
% 48.75/36.96  tff(c_136, plain, (![A_238, B_239, C_240]: (k9_subset_1(A_238, B_239, C_240)=k3_xboole_0(B_239, C_240) | ~m1_subset_1(C_240, k1_zfmisc_1(A_238)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 48.75/36.96  tff(c_147, plain, (![B_239]: (k9_subset_1('#skF_1', B_239, '#skF_4')=k3_xboole_0(B_239, '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_136])).
% 48.75/36.96  tff(c_444, plain, (![A_261, C_262, B_263]: (k9_subset_1(A_261, C_262, B_263)=k9_subset_1(A_261, B_263, C_262) | ~m1_subset_1(C_262, k1_zfmisc_1(A_261)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 48.75/36.96  tff(c_450, plain, (![B_263]: (k9_subset_1('#skF_1', B_263, '#skF_4')=k9_subset_1('#skF_1', '#skF_4', B_263))), inference(resolution, [status(thm)], [c_56, c_444])).
% 48.75/36.96  tff(c_461, plain, (![B_264]: (k9_subset_1('#skF_1', '#skF_4', B_264)=k3_xboole_0(B_264, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_450])).
% 48.75/36.96  tff(c_148, plain, (![B_239]: (k9_subset_1('#skF_1', B_239, '#skF_3')=k3_xboole_0(B_239, '#skF_3'))), inference(resolution, [status(thm)], [c_60, c_136])).
% 48.75/36.96  tff(c_468, plain, (k3_xboole_0('#skF_3', '#skF_4')=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_461, c_148])).
% 48.75/36.96  tff(c_127, plain, (![A_236, B_237]: (r1_xboole_0(A_236, B_237) | ~r1_subset_1(A_236, B_237) | v1_xboole_0(B_237) | v1_xboole_0(A_236))), inference(cnfTransformation, [status(thm)], [f_63])).
% 48.75/36.96  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 48.75/36.96  tff(c_727, plain, (![A_291, B_292]: (k3_xboole_0(A_291, B_292)=k1_xboole_0 | ~r1_subset_1(A_291, B_292) | v1_xboole_0(B_292) | v1_xboole_0(A_291))), inference(resolution, [status(thm)], [c_127, c_2])).
% 48.75/36.96  tff(c_730, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_727])).
% 48.75/36.96  tff(c_732, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_468, c_730])).
% 48.75/36.96  tff(c_733, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_732])).
% 48.75/36.96  tff(c_93, plain, (![C_231, A_232, B_233]: (v4_relat_1(C_231, A_232) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 48.75/36.96  tff(c_100, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_93])).
% 48.75/36.96  tff(c_104, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_100, c_14])).
% 48.75/36.96  tff(c_107, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_104])).
% 48.75/36.96  tff(c_279, plain, (![C_252, A_253, B_254]: (k7_relat_1(k7_relat_1(C_252, A_253), B_254)=k7_relat_1(C_252, k3_xboole_0(A_253, B_254)) | ~v1_relat_1(C_252))), inference(cnfTransformation, [status(thm)], [f_41])).
% 48.75/36.96  tff(c_315, plain, (![B_254]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', B_254))=k7_relat_1('#skF_6', B_254) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_279])).
% 48.75/36.96  tff(c_325, plain, (![B_254]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', B_254))=k7_relat_1('#skF_6', B_254))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_315])).
% 48.75/36.96  tff(c_752, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_733, c_325])).
% 48.75/36.96  tff(c_739, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_733, c_468])).
% 48.75/36.96  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 48.75/36.96  tff(c_177, plain, (![C_244, A_245, B_246]: (k7_relat_1(k7_relat_1(C_244, A_245), B_246)=k1_xboole_0 | ~r1_xboole_0(A_245, B_246) | ~v1_relat_1(C_244))), inference(cnfTransformation, [status(thm)], [f_47])).
% 48.75/36.96  tff(c_195, plain, (![B_246]: (k7_relat_1('#skF_6', B_246)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_246) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_177])).
% 48.75/36.96  tff(c_215, plain, (![B_248]: (k7_relat_1('#skF_6', B_248)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_248))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_195])).
% 48.75/36.96  tff(c_227, plain, (![B_2]: (k7_relat_1('#skF_6', B_2)=k1_xboole_0 | k3_xboole_0('#skF_4', B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_215])).
% 48.75/36.96  tff(c_10, plain, (![C_11, A_9, B_10]: (k7_relat_1(k7_relat_1(C_11, A_9), B_10)=k7_relat_1(C_11, k3_xboole_0(A_9, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 48.75/36.96  tff(c_804, plain, (![B_10]: (k7_relat_1(k7_relat_1('#skF_6', '#skF_3'), B_10)=k7_relat_1('#skF_6', k3_xboole_0(k1_xboole_0, B_10)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_752, c_10])).
% 48.75/36.96  tff(c_1044, plain, (![B_327]: (k7_relat_1(k7_relat_1('#skF_6', '#skF_3'), B_327)=k7_relat_1('#skF_6', k3_xboole_0(k1_xboole_0, B_327)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_804])).
% 48.75/36.96  tff(c_1069, plain, (![B_327]: (k7_relat_1('#skF_6', k3_xboole_0(k1_xboole_0, B_327))=k7_relat_1(k1_xboole_0, B_327) | k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_227, c_1044])).
% 48.75/36.96  tff(c_1084, plain, (![B_327]: (k7_relat_1('#skF_6', k3_xboole_0(k1_xboole_0, B_327))=k7_relat_1(k1_xboole_0, B_327))), inference(demodulation, [status(thm), theory('equality')], [c_733, c_1069])).
% 48.75/36.96  tff(c_817, plain, (![B_10]: (k7_relat_1(k7_relat_1('#skF_6', '#skF_3'), B_10)=k7_relat_1('#skF_6', k3_xboole_0(k1_xboole_0, B_10)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_804])).
% 48.75/36.96  tff(c_1120, plain, (![B_330]: (k7_relat_1(k7_relat_1('#skF_6', '#skF_3'), B_330)=k7_relat_1(k1_xboole_0, B_330))), inference(demodulation, [status(thm), theory('equality')], [c_1084, c_817])).
% 48.75/36.96  tff(c_1129, plain, (![B_330]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_330))=k7_relat_1(k1_xboole_0, B_330) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1120, c_10])).
% 48.75/36.96  tff(c_1179, plain, (![B_337]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_337))=k7_relat_1(k1_xboole_0, B_337))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1129])).
% 48.75/36.96  tff(c_1197, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k7_relat_1('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_739, c_1179])).
% 48.75/36.96  tff(c_1207, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k7_relat_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_752, c_1197])).
% 48.75/36.96  tff(c_12, plain, (![C_14, A_12, B_13]: (k7_relat_1(k7_relat_1(C_14, A_12), B_13)=k1_xboole_0 | ~r1_xboole_0(A_12, B_13) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 48.75/36.96  tff(c_1135, plain, (![B_330]: (k7_relat_1(k1_xboole_0, B_330)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_330) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1120, c_12])).
% 48.75/36.96  tff(c_1164, plain, (![B_331]: (k7_relat_1(k1_xboole_0, B_331)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_331))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1135])).
% 48.75/36.96  tff(c_1168, plain, (![B_18]: (k7_relat_1(k1_xboole_0, B_18)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_1164])).
% 48.75/36.96  tff(c_1233, plain, (![B_338]: (k7_relat_1(k1_xboole_0, B_338)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_338) | v1_xboole_0(B_338))), inference(negUnitSimplification, [status(thm)], [c_62, c_1168])).
% 48.75/36.96  tff(c_1236, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_1233])).
% 48.75/36.96  tff(c_1238, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1207, c_1236])).
% 48.75/36.96  tff(c_1239, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_1238])).
% 48.75/36.96  tff(c_1242, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1239, c_752])).
% 48.75/36.96  tff(c_589, plain, (![A_268, B_269, C_270, D_271]: (k2_partfun1(A_268, B_269, C_270, D_271)=k7_relat_1(C_270, D_271) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_268, B_269))) | ~v1_funct_1(C_270))), inference(cnfTransformation, [status(thm)], [f_79])).
% 48.75/36.96  tff(c_591, plain, (![D_271]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_271)=k7_relat_1('#skF_6', D_271) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_42, c_589])).
% 48.75/36.96  tff(c_596, plain, (![D_271]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_271)=k7_relat_1('#skF_6', D_271))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_591])).
% 48.75/36.96  tff(c_101, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_93])).
% 48.75/36.96  tff(c_115, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_101, c_14])).
% 48.75/36.96  tff(c_118, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_115])).
% 48.75/36.96  tff(c_192, plain, (![B_246]: (k7_relat_1('#skF_5', B_246)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_246) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_118, c_177])).
% 48.75/36.96  tff(c_202, plain, (![B_247]: (k7_relat_1('#skF_5', B_247)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_247))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_192])).
% 48.75/36.96  tff(c_206, plain, (![B_18]: (k7_relat_1('#skF_5', B_18)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_202])).
% 48.75/36.96  tff(c_377, plain, (![B_258]: (k7_relat_1('#skF_5', B_258)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_258) | v1_xboole_0(B_258))), inference(negUnitSimplification, [status(thm)], [c_62, c_206])).
% 48.75/36.96  tff(c_380, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_377])).
% 48.75/36.96  tff(c_383, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_380])).
% 48.75/36.96  tff(c_312, plain, (![B_254]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', B_254))=k7_relat_1('#skF_5', B_254) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_118, c_279])).
% 48.75/36.96  tff(c_323, plain, (![B_254]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', B_254))=k7_relat_1('#skF_5', B_254))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_312])).
% 48.75/36.96  tff(c_491, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3'))=k7_relat_1('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_468, c_323])).
% 48.75/36.96  tff(c_494, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_383, c_491])).
% 48.75/36.96  tff(c_738, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_733, c_494])).
% 48.75/36.96  tff(c_593, plain, (![D_271]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_271)=k7_relat_1('#skF_5', D_271) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_589])).
% 48.75/36.96  tff(c_599, plain, (![D_271]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_271)=k7_relat_1('#skF_5', D_271))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_593])).
% 48.75/36.96  tff(c_40, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 48.75/36.96  tff(c_83, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_40])).
% 48.75/36.96  tff(c_149, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_147, c_83])).
% 48.75/36.96  tff(c_1726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1242, c_596, c_738, c_599, c_739, c_739, c_149])).
% 48.75/36.96  tff(c_1728, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_40])).
% 48.75/36.96  tff(c_1798, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1796, c_1796, c_1728])).
% 48.75/36.96  tff(c_51013, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2027, c_1910, c_2112, c_2025, c_2158, c_2161, c_1798])).
% 48.75/36.96  tff(c_1771, plain, (![A_380, B_381]: (r1_xboole_0(A_380, B_381) | ~r1_subset_1(A_380, B_381) | v1_xboole_0(B_381) | v1_xboole_0(A_380))), inference(cnfTransformation, [status(thm)], [f_63])).
% 48.75/36.96  tff(c_51172, plain, (![A_1734, B_1735]: (k3_xboole_0(A_1734, B_1735)=k1_xboole_0 | ~r1_subset_1(A_1734, B_1735) | v1_xboole_0(B_1735) | v1_xboole_0(A_1734))), inference(resolution, [status(thm)], [c_1771, c_2])).
% 48.75/36.96  tff(c_51175, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_51172])).
% 48.75/36.96  tff(c_51177, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1910, c_51175])).
% 48.75/36.96  tff(c_51178, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_51177])).
% 48.75/36.96  tff(c_51196, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_51178, c_2027])).
% 48.75/36.96  tff(c_51202, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_51013, c_51196])).
% 48.75/36.96  tff(c_1894, plain, (![B_398]: (k9_subset_1('#skF_1', B_398, '#skF_3')=k9_subset_1('#skF_1', '#skF_3', B_398))), inference(resolution, [status(thm)], [c_60, c_1886])).
% 48.75/36.96  tff(c_1902, plain, (![B_398]: (k9_subset_1('#skF_1', '#skF_3', B_398)=k3_xboole_0(B_398, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1797, c_1894])).
% 48.75/36.96  tff(c_2028, plain, (![B_406]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', B_406))=k7_relat_1('#skF_5', B_406))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_2016])).
% 48.75/36.96  tff(c_2049, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3'))=k7_relat_1('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1910, c_2028])).
% 48.75/36.96  tff(c_2180, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2112, c_2049])).
% 48.75/36.96  tff(c_51182, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_51178, c_2180])).
% 48.75/36.96  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 48.75/36.96  tff(c_64, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 48.75/36.96  tff(c_44, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 48.75/36.96  tff(c_51204, plain, (![B_1739, D_1740, A_1741, F_1736, C_1738, E_1737]: (v1_funct_1(k1_tmap_1(A_1741, B_1739, C_1738, D_1740, E_1737, F_1736)) | ~m1_subset_1(F_1736, k1_zfmisc_1(k2_zfmisc_1(D_1740, B_1739))) | ~v1_funct_2(F_1736, D_1740, B_1739) | ~v1_funct_1(F_1736) | ~m1_subset_1(E_1737, k1_zfmisc_1(k2_zfmisc_1(C_1738, B_1739))) | ~v1_funct_2(E_1737, C_1738, B_1739) | ~v1_funct_1(E_1737) | ~m1_subset_1(D_1740, k1_zfmisc_1(A_1741)) | v1_xboole_0(D_1740) | ~m1_subset_1(C_1738, k1_zfmisc_1(A_1741)) | v1_xboole_0(C_1738) | v1_xboole_0(B_1739) | v1_xboole_0(A_1741))), inference(cnfTransformation, [status(thm)], [f_161])).
% 48.75/36.96  tff(c_51206, plain, (![A_1741, C_1738, E_1737]: (v1_funct_1(k1_tmap_1(A_1741, '#skF_2', C_1738, '#skF_4', E_1737, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1737, k1_zfmisc_1(k2_zfmisc_1(C_1738, '#skF_2'))) | ~v1_funct_2(E_1737, C_1738, '#skF_2') | ~v1_funct_1(E_1737) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1741)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1738, k1_zfmisc_1(A_1741)) | v1_xboole_0(C_1738) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1741))), inference(resolution, [status(thm)], [c_42, c_51204])).
% 48.75/36.96  tff(c_51211, plain, (![A_1741, C_1738, E_1737]: (v1_funct_1(k1_tmap_1(A_1741, '#skF_2', C_1738, '#skF_4', E_1737, '#skF_6')) | ~m1_subset_1(E_1737, k1_zfmisc_1(k2_zfmisc_1(C_1738, '#skF_2'))) | ~v1_funct_2(E_1737, C_1738, '#skF_2') | ~v1_funct_1(E_1737) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1741)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1738, k1_zfmisc_1(A_1741)) | v1_xboole_0(C_1738) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1741))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_51206])).
% 48.75/36.96  tff(c_51562, plain, (![A_1785, C_1786, E_1787]: (v1_funct_1(k1_tmap_1(A_1785, '#skF_2', C_1786, '#skF_4', E_1787, '#skF_6')) | ~m1_subset_1(E_1787, k1_zfmisc_1(k2_zfmisc_1(C_1786, '#skF_2'))) | ~v1_funct_2(E_1787, C_1786, '#skF_2') | ~v1_funct_1(E_1787) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1785)) | ~m1_subset_1(C_1786, k1_zfmisc_1(A_1785)) | v1_xboole_0(C_1786) | v1_xboole_0(A_1785))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_51211])).
% 48.75/36.96  tff(c_51569, plain, (![A_1785]: (v1_funct_1(k1_tmap_1(A_1785, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1785)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1785)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1785))), inference(resolution, [status(thm)], [c_48, c_51562])).
% 48.75/36.96  tff(c_51579, plain, (![A_1785]: (v1_funct_1(k1_tmap_1(A_1785, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1785)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1785)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1785))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_51569])).
% 48.75/36.96  tff(c_52024, plain, (![A_1820]: (v1_funct_1(k1_tmap_1(A_1820, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1820)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1820)) | v1_xboole_0(A_1820))), inference(negUnitSimplification, [status(thm)], [c_62, c_51579])).
% 48.75/36.96  tff(c_52027, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_52024])).
% 48.75/36.96  tff(c_52030, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52027])).
% 48.75/36.96  tff(c_52031, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_66, c_52030])).
% 48.75/36.96  tff(c_36, plain, (![C_158, A_156, D_159, B_157, F_161, E_160]: (v1_funct_2(k1_tmap_1(A_156, B_157, C_158, D_159, E_160, F_161), k4_subset_1(A_156, C_158, D_159), B_157) | ~m1_subset_1(F_161, k1_zfmisc_1(k2_zfmisc_1(D_159, B_157))) | ~v1_funct_2(F_161, D_159, B_157) | ~v1_funct_1(F_161) | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(C_158, B_157))) | ~v1_funct_2(E_160, C_158, B_157) | ~v1_funct_1(E_160) | ~m1_subset_1(D_159, k1_zfmisc_1(A_156)) | v1_xboole_0(D_159) | ~m1_subset_1(C_158, k1_zfmisc_1(A_156)) | v1_xboole_0(C_158) | v1_xboole_0(B_157) | v1_xboole_0(A_156))), inference(cnfTransformation, [status(thm)], [f_161])).
% 48.75/36.96  tff(c_34, plain, (![C_158, A_156, D_159, B_157, F_161, E_160]: (m1_subset_1(k1_tmap_1(A_156, B_157, C_158, D_159, E_160, F_161), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_156, C_158, D_159), B_157))) | ~m1_subset_1(F_161, k1_zfmisc_1(k2_zfmisc_1(D_159, B_157))) | ~v1_funct_2(F_161, D_159, B_157) | ~v1_funct_1(F_161) | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(C_158, B_157))) | ~v1_funct_2(E_160, C_158, B_157) | ~v1_funct_1(E_160) | ~m1_subset_1(D_159, k1_zfmisc_1(A_156)) | v1_xboole_0(D_159) | ~m1_subset_1(C_158, k1_zfmisc_1(A_156)) | v1_xboole_0(C_158) | v1_xboole_0(B_157) | v1_xboole_0(A_156))), inference(cnfTransformation, [status(thm)], [f_161])).
% 48.75/36.96  tff(c_51626, plain, (![D_1794, C_1792, F_1793, E_1796, B_1797, A_1795]: (k2_partfun1(k4_subset_1(A_1795, C_1792, D_1794), B_1797, k1_tmap_1(A_1795, B_1797, C_1792, D_1794, E_1796, F_1793), C_1792)=E_1796 | ~m1_subset_1(k1_tmap_1(A_1795, B_1797, C_1792, D_1794, E_1796, F_1793), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1795, C_1792, D_1794), B_1797))) | ~v1_funct_2(k1_tmap_1(A_1795, B_1797, C_1792, D_1794, E_1796, F_1793), k4_subset_1(A_1795, C_1792, D_1794), B_1797) | ~v1_funct_1(k1_tmap_1(A_1795, B_1797, C_1792, D_1794, E_1796, F_1793)) | k2_partfun1(D_1794, B_1797, F_1793, k9_subset_1(A_1795, C_1792, D_1794))!=k2_partfun1(C_1792, B_1797, E_1796, k9_subset_1(A_1795, C_1792, D_1794)) | ~m1_subset_1(F_1793, k1_zfmisc_1(k2_zfmisc_1(D_1794, B_1797))) | ~v1_funct_2(F_1793, D_1794, B_1797) | ~v1_funct_1(F_1793) | ~m1_subset_1(E_1796, k1_zfmisc_1(k2_zfmisc_1(C_1792, B_1797))) | ~v1_funct_2(E_1796, C_1792, B_1797) | ~v1_funct_1(E_1796) | ~m1_subset_1(D_1794, k1_zfmisc_1(A_1795)) | v1_xboole_0(D_1794) | ~m1_subset_1(C_1792, k1_zfmisc_1(A_1795)) | v1_xboole_0(C_1792) | v1_xboole_0(B_1797) | v1_xboole_0(A_1795))), inference(cnfTransformation, [status(thm)], [f_127])).
% 48.75/36.96  tff(c_116122, plain, (![E_3252, B_3254, A_3256, D_3255, C_3253, F_3251]: (k2_partfun1(k4_subset_1(A_3256, C_3253, D_3255), B_3254, k1_tmap_1(A_3256, B_3254, C_3253, D_3255, E_3252, F_3251), C_3253)=E_3252 | ~v1_funct_2(k1_tmap_1(A_3256, B_3254, C_3253, D_3255, E_3252, F_3251), k4_subset_1(A_3256, C_3253, D_3255), B_3254) | ~v1_funct_1(k1_tmap_1(A_3256, B_3254, C_3253, D_3255, E_3252, F_3251)) | k2_partfun1(D_3255, B_3254, F_3251, k9_subset_1(A_3256, C_3253, D_3255))!=k2_partfun1(C_3253, B_3254, E_3252, k9_subset_1(A_3256, C_3253, D_3255)) | ~m1_subset_1(F_3251, k1_zfmisc_1(k2_zfmisc_1(D_3255, B_3254))) | ~v1_funct_2(F_3251, D_3255, B_3254) | ~v1_funct_1(F_3251) | ~m1_subset_1(E_3252, k1_zfmisc_1(k2_zfmisc_1(C_3253, B_3254))) | ~v1_funct_2(E_3252, C_3253, B_3254) | ~v1_funct_1(E_3252) | ~m1_subset_1(D_3255, k1_zfmisc_1(A_3256)) | v1_xboole_0(D_3255) | ~m1_subset_1(C_3253, k1_zfmisc_1(A_3256)) | v1_xboole_0(C_3253) | v1_xboole_0(B_3254) | v1_xboole_0(A_3256))), inference(resolution, [status(thm)], [c_34, c_51626])).
% 48.75/36.96  tff(c_145582, plain, (![C_3932, D_3934, B_3933, F_3930, A_3935, E_3931]: (k2_partfun1(k4_subset_1(A_3935, C_3932, D_3934), B_3933, k1_tmap_1(A_3935, B_3933, C_3932, D_3934, E_3931, F_3930), C_3932)=E_3931 | ~v1_funct_1(k1_tmap_1(A_3935, B_3933, C_3932, D_3934, E_3931, F_3930)) | k2_partfun1(D_3934, B_3933, F_3930, k9_subset_1(A_3935, C_3932, D_3934))!=k2_partfun1(C_3932, B_3933, E_3931, k9_subset_1(A_3935, C_3932, D_3934)) | ~m1_subset_1(F_3930, k1_zfmisc_1(k2_zfmisc_1(D_3934, B_3933))) | ~v1_funct_2(F_3930, D_3934, B_3933) | ~v1_funct_1(F_3930) | ~m1_subset_1(E_3931, k1_zfmisc_1(k2_zfmisc_1(C_3932, B_3933))) | ~v1_funct_2(E_3931, C_3932, B_3933) | ~v1_funct_1(E_3931) | ~m1_subset_1(D_3934, k1_zfmisc_1(A_3935)) | v1_xboole_0(D_3934) | ~m1_subset_1(C_3932, k1_zfmisc_1(A_3935)) | v1_xboole_0(C_3932) | v1_xboole_0(B_3933) | v1_xboole_0(A_3935))), inference(resolution, [status(thm)], [c_36, c_116122])).
% 48.75/36.96  tff(c_145586, plain, (![A_3935, C_3932, E_3931]: (k2_partfun1(k4_subset_1(A_3935, C_3932, '#skF_4'), '#skF_2', k1_tmap_1(A_3935, '#skF_2', C_3932, '#skF_4', E_3931, '#skF_6'), C_3932)=E_3931 | ~v1_funct_1(k1_tmap_1(A_3935, '#skF_2', C_3932, '#skF_4', E_3931, '#skF_6')) | k2_partfun1(C_3932, '#skF_2', E_3931, k9_subset_1(A_3935, C_3932, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_3935, C_3932, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_3931, k1_zfmisc_1(k2_zfmisc_1(C_3932, '#skF_2'))) | ~v1_funct_2(E_3931, C_3932, '#skF_2') | ~v1_funct_1(E_3931) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3935)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3932, k1_zfmisc_1(A_3935)) | v1_xboole_0(C_3932) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3935))), inference(resolution, [status(thm)], [c_42, c_145582])).
% 48.75/36.96  tff(c_145592, plain, (![A_3935, C_3932, E_3931]: (k2_partfun1(k4_subset_1(A_3935, C_3932, '#skF_4'), '#skF_2', k1_tmap_1(A_3935, '#skF_2', C_3932, '#skF_4', E_3931, '#skF_6'), C_3932)=E_3931 | ~v1_funct_1(k1_tmap_1(A_3935, '#skF_2', C_3932, '#skF_4', E_3931, '#skF_6')) | k2_partfun1(C_3932, '#skF_2', E_3931, k9_subset_1(A_3935, C_3932, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3935, C_3932, '#skF_4')) | ~m1_subset_1(E_3931, k1_zfmisc_1(k2_zfmisc_1(C_3932, '#skF_2'))) | ~v1_funct_2(E_3931, C_3932, '#skF_2') | ~v1_funct_1(E_3931) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3935)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3932, k1_zfmisc_1(A_3935)) | v1_xboole_0(C_3932) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3935))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_2158, c_145586])).
% 48.75/36.96  tff(c_155709, plain, (![A_4189, C_4190, E_4191]: (k2_partfun1(k4_subset_1(A_4189, C_4190, '#skF_4'), '#skF_2', k1_tmap_1(A_4189, '#skF_2', C_4190, '#skF_4', E_4191, '#skF_6'), C_4190)=E_4191 | ~v1_funct_1(k1_tmap_1(A_4189, '#skF_2', C_4190, '#skF_4', E_4191, '#skF_6')) | k2_partfun1(C_4190, '#skF_2', E_4191, k9_subset_1(A_4189, C_4190, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4189, C_4190, '#skF_4')) | ~m1_subset_1(E_4191, k1_zfmisc_1(k2_zfmisc_1(C_4190, '#skF_2'))) | ~v1_funct_2(E_4191, C_4190, '#skF_2') | ~v1_funct_1(E_4191) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4189)) | ~m1_subset_1(C_4190, k1_zfmisc_1(A_4189)) | v1_xboole_0(C_4190) | v1_xboole_0(A_4189))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_145592])).
% 48.75/36.96  tff(c_155716, plain, (![A_4189]: (k2_partfun1(k4_subset_1(A_4189, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_4189, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_4189, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_4189, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4189, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4189)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4189)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4189))), inference(resolution, [status(thm)], [c_48, c_155709])).
% 48.75/36.96  tff(c_155726, plain, (![A_4189]: (k2_partfun1(k4_subset_1(A_4189, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_4189, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_4189, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_4189, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4189, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4189)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4189)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4189))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2161, c_155716])).
% 48.75/36.96  tff(c_159426, plain, (![A_4219]: (k2_partfun1(k4_subset_1(A_4219, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_4219, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_4219, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_4219, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4219, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4219)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4219)) | v1_xboole_0(A_4219))), inference(negUnitSimplification, [status(thm)], [c_62, c_155726])).
% 48.75/36.96  tff(c_2320, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2180, c_2161, c_2027, c_2158, c_1910, c_1910, c_1798])).
% 48.75/36.96  tff(c_2511, plain, (![A_442, B_443]: (k3_xboole_0(A_442, B_443)=k1_xboole_0 | ~r1_subset_1(A_442, B_443) | v1_xboole_0(B_443) | v1_xboole_0(A_442))), inference(resolution, [status(thm)], [c_1771, c_2])).
% 48.75/36.96  tff(c_2514, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_2511])).
% 48.75/36.96  tff(c_2516, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1910, c_2514])).
% 48.75/36.96  tff(c_2517, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_2516])).
% 48.75/36.96  tff(c_2535, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2517, c_2027])).
% 48.75/36.96  tff(c_2541, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2320, c_2535])).
% 48.75/36.96  tff(c_2521, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2517, c_2180])).
% 48.75/36.96  tff(c_2484, plain, (![D_436, B_435, A_437, E_433, F_432, C_434]: (v1_funct_1(k1_tmap_1(A_437, B_435, C_434, D_436, E_433, F_432)) | ~m1_subset_1(F_432, k1_zfmisc_1(k2_zfmisc_1(D_436, B_435))) | ~v1_funct_2(F_432, D_436, B_435) | ~v1_funct_1(F_432) | ~m1_subset_1(E_433, k1_zfmisc_1(k2_zfmisc_1(C_434, B_435))) | ~v1_funct_2(E_433, C_434, B_435) | ~v1_funct_1(E_433) | ~m1_subset_1(D_436, k1_zfmisc_1(A_437)) | v1_xboole_0(D_436) | ~m1_subset_1(C_434, k1_zfmisc_1(A_437)) | v1_xboole_0(C_434) | v1_xboole_0(B_435) | v1_xboole_0(A_437))), inference(cnfTransformation, [status(thm)], [f_161])).
% 48.75/36.96  tff(c_2486, plain, (![A_437, C_434, E_433]: (v1_funct_1(k1_tmap_1(A_437, '#skF_2', C_434, '#skF_4', E_433, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_433, k1_zfmisc_1(k2_zfmisc_1(C_434, '#skF_2'))) | ~v1_funct_2(E_433, C_434, '#skF_2') | ~v1_funct_1(E_433) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_437)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_434, k1_zfmisc_1(A_437)) | v1_xboole_0(C_434) | v1_xboole_0('#skF_2') | v1_xboole_0(A_437))), inference(resolution, [status(thm)], [c_42, c_2484])).
% 48.75/36.96  tff(c_2491, plain, (![A_437, C_434, E_433]: (v1_funct_1(k1_tmap_1(A_437, '#skF_2', C_434, '#skF_4', E_433, '#skF_6')) | ~m1_subset_1(E_433, k1_zfmisc_1(k2_zfmisc_1(C_434, '#skF_2'))) | ~v1_funct_2(E_433, C_434, '#skF_2') | ~v1_funct_1(E_433) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_437)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_434, k1_zfmisc_1(A_437)) | v1_xboole_0(C_434) | v1_xboole_0('#skF_2') | v1_xboole_0(A_437))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_2486])).
% 48.75/36.96  tff(c_2816, plain, (![A_474, C_475, E_476]: (v1_funct_1(k1_tmap_1(A_474, '#skF_2', C_475, '#skF_4', E_476, '#skF_6')) | ~m1_subset_1(E_476, k1_zfmisc_1(k2_zfmisc_1(C_475, '#skF_2'))) | ~v1_funct_2(E_476, C_475, '#skF_2') | ~v1_funct_1(E_476) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_474)) | ~m1_subset_1(C_475, k1_zfmisc_1(A_474)) | v1_xboole_0(C_475) | v1_xboole_0(A_474))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_2491])).
% 48.75/36.96  tff(c_2823, plain, (![A_474]: (v1_funct_1(k1_tmap_1(A_474, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_474)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_474)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_474))), inference(resolution, [status(thm)], [c_48, c_2816])).
% 48.75/36.96  tff(c_2833, plain, (![A_474]: (v1_funct_1(k1_tmap_1(A_474, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_474)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_474)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_474))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2823])).
% 48.75/36.96  tff(c_3116, plain, (![A_511]: (v1_funct_1(k1_tmap_1(A_511, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_511)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_511)) | v1_xboole_0(A_511))), inference(negUnitSimplification, [status(thm)], [c_62, c_2833])).
% 48.75/36.96  tff(c_3119, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_3116])).
% 48.75/36.96  tff(c_3122, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3119])).
% 48.75/36.96  tff(c_3123, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_66, c_3122])).
% 48.75/36.96  tff(c_2884, plain, (![F_486, D_487, A_488, B_490, E_489, C_485]: (k2_partfun1(k4_subset_1(A_488, C_485, D_487), B_490, k1_tmap_1(A_488, B_490, C_485, D_487, E_489, F_486), D_487)=F_486 | ~m1_subset_1(k1_tmap_1(A_488, B_490, C_485, D_487, E_489, F_486), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_488, C_485, D_487), B_490))) | ~v1_funct_2(k1_tmap_1(A_488, B_490, C_485, D_487, E_489, F_486), k4_subset_1(A_488, C_485, D_487), B_490) | ~v1_funct_1(k1_tmap_1(A_488, B_490, C_485, D_487, E_489, F_486)) | k2_partfun1(D_487, B_490, F_486, k9_subset_1(A_488, C_485, D_487))!=k2_partfun1(C_485, B_490, E_489, k9_subset_1(A_488, C_485, D_487)) | ~m1_subset_1(F_486, k1_zfmisc_1(k2_zfmisc_1(D_487, B_490))) | ~v1_funct_2(F_486, D_487, B_490) | ~v1_funct_1(F_486) | ~m1_subset_1(E_489, k1_zfmisc_1(k2_zfmisc_1(C_485, B_490))) | ~v1_funct_2(E_489, C_485, B_490) | ~v1_funct_1(E_489) | ~m1_subset_1(D_487, k1_zfmisc_1(A_488)) | v1_xboole_0(D_487) | ~m1_subset_1(C_485, k1_zfmisc_1(A_488)) | v1_xboole_0(C_485) | v1_xboole_0(B_490) | v1_xboole_0(A_488))), inference(cnfTransformation, [status(thm)], [f_127])).
% 48.75/36.96  tff(c_7446, plain, (![A_715, B_713, F_710, C_712, D_714, E_711]: (k2_partfun1(k4_subset_1(A_715, C_712, D_714), B_713, k1_tmap_1(A_715, B_713, C_712, D_714, E_711, F_710), D_714)=F_710 | ~v1_funct_2(k1_tmap_1(A_715, B_713, C_712, D_714, E_711, F_710), k4_subset_1(A_715, C_712, D_714), B_713) | ~v1_funct_1(k1_tmap_1(A_715, B_713, C_712, D_714, E_711, F_710)) | k2_partfun1(D_714, B_713, F_710, k9_subset_1(A_715, C_712, D_714))!=k2_partfun1(C_712, B_713, E_711, k9_subset_1(A_715, C_712, D_714)) | ~m1_subset_1(F_710, k1_zfmisc_1(k2_zfmisc_1(D_714, B_713))) | ~v1_funct_2(F_710, D_714, B_713) | ~v1_funct_1(F_710) | ~m1_subset_1(E_711, k1_zfmisc_1(k2_zfmisc_1(C_712, B_713))) | ~v1_funct_2(E_711, C_712, B_713) | ~v1_funct_1(E_711) | ~m1_subset_1(D_714, k1_zfmisc_1(A_715)) | v1_xboole_0(D_714) | ~m1_subset_1(C_712, k1_zfmisc_1(A_715)) | v1_xboole_0(C_712) | v1_xboole_0(B_713) | v1_xboole_0(A_715))), inference(resolution, [status(thm)], [c_34, c_2884])).
% 48.75/36.96  tff(c_36570, plain, (![B_1414, E_1412, C_1413, F_1411, A_1416, D_1415]: (k2_partfun1(k4_subset_1(A_1416, C_1413, D_1415), B_1414, k1_tmap_1(A_1416, B_1414, C_1413, D_1415, E_1412, F_1411), D_1415)=F_1411 | ~v1_funct_1(k1_tmap_1(A_1416, B_1414, C_1413, D_1415, E_1412, F_1411)) | k2_partfun1(D_1415, B_1414, F_1411, k9_subset_1(A_1416, C_1413, D_1415))!=k2_partfun1(C_1413, B_1414, E_1412, k9_subset_1(A_1416, C_1413, D_1415)) | ~m1_subset_1(F_1411, k1_zfmisc_1(k2_zfmisc_1(D_1415, B_1414))) | ~v1_funct_2(F_1411, D_1415, B_1414) | ~v1_funct_1(F_1411) | ~m1_subset_1(E_1412, k1_zfmisc_1(k2_zfmisc_1(C_1413, B_1414))) | ~v1_funct_2(E_1412, C_1413, B_1414) | ~v1_funct_1(E_1412) | ~m1_subset_1(D_1415, k1_zfmisc_1(A_1416)) | v1_xboole_0(D_1415) | ~m1_subset_1(C_1413, k1_zfmisc_1(A_1416)) | v1_xboole_0(C_1413) | v1_xboole_0(B_1414) | v1_xboole_0(A_1416))), inference(resolution, [status(thm)], [c_36, c_7446])).
% 48.75/36.96  tff(c_36574, plain, (![A_1416, C_1413, E_1412]: (k2_partfun1(k4_subset_1(A_1416, C_1413, '#skF_4'), '#skF_2', k1_tmap_1(A_1416, '#skF_2', C_1413, '#skF_4', E_1412, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1416, '#skF_2', C_1413, '#skF_4', E_1412, '#skF_6')) | k2_partfun1(C_1413, '#skF_2', E_1412, k9_subset_1(A_1416, C_1413, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1416, C_1413, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1412, k1_zfmisc_1(k2_zfmisc_1(C_1413, '#skF_2'))) | ~v1_funct_2(E_1412, C_1413, '#skF_2') | ~v1_funct_1(E_1412) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1416)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1413, k1_zfmisc_1(A_1416)) | v1_xboole_0(C_1413) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1416))), inference(resolution, [status(thm)], [c_42, c_36570])).
% 48.75/36.96  tff(c_36580, plain, (![A_1416, C_1413, E_1412]: (k2_partfun1(k4_subset_1(A_1416, C_1413, '#skF_4'), '#skF_2', k1_tmap_1(A_1416, '#skF_2', C_1413, '#skF_4', E_1412, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1416, '#skF_2', C_1413, '#skF_4', E_1412, '#skF_6')) | k2_partfun1(C_1413, '#skF_2', E_1412, k9_subset_1(A_1416, C_1413, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1416, C_1413, '#skF_4')) | ~m1_subset_1(E_1412, k1_zfmisc_1(k2_zfmisc_1(C_1413, '#skF_2'))) | ~v1_funct_2(E_1412, C_1413, '#skF_2') | ~v1_funct_1(E_1412) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1416)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1413, k1_zfmisc_1(A_1416)) | v1_xboole_0(C_1413) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1416))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_2158, c_36574])).
% 48.75/36.96  tff(c_48586, plain, (![A_1669, C_1670, E_1671]: (k2_partfun1(k4_subset_1(A_1669, C_1670, '#skF_4'), '#skF_2', k1_tmap_1(A_1669, '#skF_2', C_1670, '#skF_4', E_1671, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1669, '#skF_2', C_1670, '#skF_4', E_1671, '#skF_6')) | k2_partfun1(C_1670, '#skF_2', E_1671, k9_subset_1(A_1669, C_1670, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1669, C_1670, '#skF_4')) | ~m1_subset_1(E_1671, k1_zfmisc_1(k2_zfmisc_1(C_1670, '#skF_2'))) | ~v1_funct_2(E_1671, C_1670, '#skF_2') | ~v1_funct_1(E_1671) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1669)) | ~m1_subset_1(C_1670, k1_zfmisc_1(A_1669)) | v1_xboole_0(C_1670) | v1_xboole_0(A_1669))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_36580])).
% 48.75/36.96  tff(c_48593, plain, (![A_1669]: (k2_partfun1(k4_subset_1(A_1669, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1669, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1669, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1669, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1669, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1669)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1669)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1669))), inference(resolution, [status(thm)], [c_48, c_48586])).
% 48.75/36.96  tff(c_48603, plain, (![A_1669]: (k2_partfun1(k4_subset_1(A_1669, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1669, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1669, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1669, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1669, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1669)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1669)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1669))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2161, c_48593])).
% 48.75/36.96  tff(c_50942, plain, (![A_1721]: (k2_partfun1(k4_subset_1(A_1721, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1721, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1721, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1721, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1721, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1721)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1721)) | v1_xboole_0(A_1721))), inference(negUnitSimplification, [status(thm)], [c_62, c_48603])).
% 48.75/36.96  tff(c_1727, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_40])).
% 48.75/36.96  tff(c_2288, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_1727])).
% 48.75/36.96  tff(c_50953, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_50942, c_2288])).
% 48.75/36.96  tff(c_50967, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_2541, c_2517, c_1902, c_2521, c_2517, c_1902, c_3123, c_50953])).
% 48.75/36.96  tff(c_50969, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_50967])).
% 48.75/36.96  tff(c_50970, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_1727])).
% 48.75/36.96  tff(c_159438, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_159426, c_50970])).
% 48.75/36.96  tff(c_159452, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_51202, c_51178, c_1902, c_51182, c_51178, c_1902, c_52031, c_159438])).
% 48.75/36.96  tff(c_159454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_159452])).
% 48.75/36.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.75/36.96  
% 48.75/36.96  Inference rules
% 48.75/36.96  ----------------------
% 48.75/36.96  #Ref     : 0
% 48.75/36.96  #Sup     : 39312
% 48.75/36.96  #Fact    : 0
% 48.75/36.96  #Define  : 0
% 48.75/36.96  #Split   : 89
% 48.75/36.96  #Chain   : 0
% 48.75/36.96  #Close   : 0
% 48.75/36.96  
% 48.75/36.96  Ordering : KBO
% 48.75/36.96  
% 48.75/36.96  Simplification rules
% 48.75/36.96  ----------------------
% 48.75/36.96  #Subsume      : 17343
% 48.75/36.96  #Demod        : 28504
% 48.75/36.96  #Tautology    : 3969
% 48.75/36.96  #SimpNegUnit  : 558
% 48.75/36.96  #BackRed      : 57
% 48.75/36.96  
% 48.75/36.96  #Partial instantiations: 0
% 48.75/36.96  #Strategies tried      : 1
% 48.75/36.96  
% 48.75/36.96  Timing (in seconds)
% 48.75/36.96  ----------------------
% 48.75/36.97  Preprocessing        : 0.45
% 48.75/36.97  Parsing              : 0.21
% 48.75/36.97  CNF conversion       : 0.07
% 48.75/36.97  Main loop            : 35.70
% 48.75/36.97  Inferencing          : 4.96
% 48.75/36.97  Reduction            : 13.26
% 48.75/36.97  Demodulation         : 11.09
% 48.75/36.97  BG Simplification    : 0.56
% 48.75/36.97  Subsumption          : 15.64
% 48.75/36.97  Abstraction          : 0.89
% 48.75/36.97  MUC search           : 0.00
% 48.75/36.97  Cooper               : 0.00
% 48.75/36.97  Total                : 36.22
% 48.75/36.97  Index Insertion      : 0.00
% 48.75/36.97  Index Deletion       : 0.00
% 48.75/36.97  Index Matching       : 0.00
% 48.75/36.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
