%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:20 EST 2020

% Result     : Theorem 9.47s
% Output     : CNFRefutation 9.47s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 452 expanded)
%              Number of leaves         :   41 ( 184 expanded)
%              Depth                    :   12
%              Number of atoms          :  589 (2534 expanded)
%              Number of equality atoms :  101 ( 444 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_208,negated_conjecture,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
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

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_74,axiom,(
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

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_166,axiom,(
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

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_132,axiom,(
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

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_46,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_83,plain,(
    ! [C_223,A_224,B_225] :
      ( v1_relat_1(C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_90,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_83])).

tff(c_400,plain,(
    ! [A_285,B_286] :
      ( r2_hidden('#skF_2'(A_285,B_286),B_286)
      | r1_xboole_0(A_285,B_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_404,plain,(
    ! [B_286,A_285] :
      ( ~ v1_xboole_0(B_286)
      | r1_xboole_0(A_285,B_286) ) ),
    inference(resolution,[status(thm)],[c_400,c_2])).

tff(c_472,plain,(
    ! [B_304,A_305] :
      ( k7_relat_1(B_304,A_305) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_304),A_305)
      | ~ v1_relat_1(B_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_492,plain,(
    ! [B_306,B_307] :
      ( k7_relat_1(B_306,B_307) = k1_xboole_0
      | ~ v1_relat_1(B_306)
      | ~ v1_xboole_0(B_307) ) ),
    inference(resolution,[status(thm)],[c_404,c_472])).

tff(c_521,plain,(
    ! [B_311] :
      ( k7_relat_1('#skF_8',B_311) = k1_xboole_0
      | ~ v1_xboole_0(B_311) ) ),
    inference(resolution,[status(thm)],[c_90,c_492])).

tff(c_525,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_521])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_58,plain,(
    r1_subset_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_499,plain,(
    ! [A_308,B_309] :
      ( r1_xboole_0(A_308,B_309)
      | ~ r1_subset_1(A_308,B_309)
      | v1_xboole_0(B_309)
      | v1_xboole_0(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2054,plain,(
    ! [A_585,B_586] :
      ( k3_xboole_0(A_585,B_586) = k1_xboole_0
      | ~ r1_subset_1(A_585,B_586)
      | v1_xboole_0(B_586)
      | v1_xboole_0(A_585) ) ),
    inference(resolution,[status(thm)],[c_499,c_6])).

tff(c_2057,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_2054])).

tff(c_2060,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_62,c_2057])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_91,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_83])).

tff(c_512,plain,(
    ! [B_310] :
      ( k7_relat_1('#skF_7',B_310) = k1_xboole_0
      | ~ v1_xboole_0(B_310) ) ),
    inference(resolution,[status(thm)],[c_91,c_492])).

tff(c_516,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_512])).

tff(c_2004,plain,(
    ! [A_578,B_579,C_580] :
      ( k9_subset_1(A_578,B_579,C_580) = k3_xboole_0(B_579,C_580)
      | ~ m1_subset_1(C_580,k1_zfmisc_1(A_578)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2015,plain,(
    ! [B_579] : k9_subset_1('#skF_3',B_579,'#skF_6') = k3_xboole_0(B_579,'#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_2004])).

tff(c_56,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_54,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_50,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_48,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_2293,plain,(
    ! [A_625,B_624,F_622,D_626,C_621,E_623] :
      ( v1_funct_1(k1_tmap_1(A_625,B_624,C_621,D_626,E_623,F_622))
      | ~ m1_subset_1(F_622,k1_zfmisc_1(k2_zfmisc_1(D_626,B_624)))
      | ~ v1_funct_2(F_622,D_626,B_624)
      | ~ v1_funct_1(F_622)
      | ~ m1_subset_1(E_623,k1_zfmisc_1(k2_zfmisc_1(C_621,B_624)))
      | ~ v1_funct_2(E_623,C_621,B_624)
      | ~ v1_funct_1(E_623)
      | ~ m1_subset_1(D_626,k1_zfmisc_1(A_625))
      | v1_xboole_0(D_626)
      | ~ m1_subset_1(C_621,k1_zfmisc_1(A_625))
      | v1_xboole_0(C_621)
      | v1_xboole_0(B_624)
      | v1_xboole_0(A_625) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2295,plain,(
    ! [A_625,C_621,E_623] :
      ( v1_funct_1(k1_tmap_1(A_625,'#skF_4',C_621,'#skF_6',E_623,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_623,k1_zfmisc_1(k2_zfmisc_1(C_621,'#skF_4')))
      | ~ v1_funct_2(E_623,C_621,'#skF_4')
      | ~ v1_funct_1(E_623)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_625))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_621,k1_zfmisc_1(A_625))
      | v1_xboole_0(C_621)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_625) ) ),
    inference(resolution,[status(thm)],[c_46,c_2293])).

tff(c_2300,plain,(
    ! [A_625,C_621,E_623] :
      ( v1_funct_1(k1_tmap_1(A_625,'#skF_4',C_621,'#skF_6',E_623,'#skF_8'))
      | ~ m1_subset_1(E_623,k1_zfmisc_1(k2_zfmisc_1(C_621,'#skF_4')))
      | ~ v1_funct_2(E_623,C_621,'#skF_4')
      | ~ v1_funct_1(E_623)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_625))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_621,k1_zfmisc_1(A_625))
      | v1_xboole_0(C_621)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_625) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2295])).

tff(c_2640,plain,(
    ! [A_700,C_701,E_702] :
      ( v1_funct_1(k1_tmap_1(A_700,'#skF_4',C_701,'#skF_6',E_702,'#skF_8'))
      | ~ m1_subset_1(E_702,k1_zfmisc_1(k2_zfmisc_1(C_701,'#skF_4')))
      | ~ v1_funct_2(E_702,C_701,'#skF_4')
      | ~ v1_funct_1(E_702)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_700))
      | ~ m1_subset_1(C_701,k1_zfmisc_1(A_700))
      | v1_xboole_0(C_701)
      | v1_xboole_0(A_700) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_2300])).

tff(c_2647,plain,(
    ! [A_700] :
      ( v1_funct_1(k1_tmap_1(A_700,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_700))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_700))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_700) ) ),
    inference(resolution,[status(thm)],[c_52,c_2640])).

tff(c_2657,plain,(
    ! [A_700] :
      ( v1_funct_1(k1_tmap_1(A_700,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_700))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_700))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_700) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2647])).

tff(c_2733,plain,(
    ! [A_725] :
      ( v1_funct_1(k1_tmap_1(A_725,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_725))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_725))
      | v1_xboole_0(A_725) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2657])).

tff(c_2736,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2733])).

tff(c_2739,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2736])).

tff(c_2740,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2739])).

tff(c_2192,plain,(
    ! [A_605,B_606,C_607,D_608] :
      ( k2_partfun1(A_605,B_606,C_607,D_608) = k7_relat_1(C_607,D_608)
      | ~ m1_subset_1(C_607,k1_zfmisc_1(k2_zfmisc_1(A_605,B_606)))
      | ~ v1_funct_1(C_607) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2196,plain,(
    ! [D_608] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_608) = k7_relat_1('#skF_7',D_608)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_52,c_2192])).

tff(c_2202,plain,(
    ! [D_608] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_608) = k7_relat_1('#skF_7',D_608) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2196])).

tff(c_2194,plain,(
    ! [D_608] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_608) = k7_relat_1('#skF_8',D_608)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_46,c_2192])).

tff(c_2199,plain,(
    ! [D_608] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_608) = k7_relat_1('#skF_8',D_608) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2194])).

tff(c_40,plain,(
    ! [F_158,C_155,D_156,E_157,A_153,B_154] :
      ( v1_funct_2(k1_tmap_1(A_153,B_154,C_155,D_156,E_157,F_158),k4_subset_1(A_153,C_155,D_156),B_154)
      | ~ m1_subset_1(F_158,k1_zfmisc_1(k2_zfmisc_1(D_156,B_154)))
      | ~ v1_funct_2(F_158,D_156,B_154)
      | ~ v1_funct_1(F_158)
      | ~ m1_subset_1(E_157,k1_zfmisc_1(k2_zfmisc_1(C_155,B_154)))
      | ~ v1_funct_2(E_157,C_155,B_154)
      | ~ v1_funct_1(E_157)
      | ~ m1_subset_1(D_156,k1_zfmisc_1(A_153))
      | v1_xboole_0(D_156)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(A_153))
      | v1_xboole_0(C_155)
      | v1_xboole_0(B_154)
      | v1_xboole_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_38,plain,(
    ! [F_158,C_155,D_156,E_157,A_153,B_154] :
      ( m1_subset_1(k1_tmap_1(A_153,B_154,C_155,D_156,E_157,F_158),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_153,C_155,D_156),B_154)))
      | ~ m1_subset_1(F_158,k1_zfmisc_1(k2_zfmisc_1(D_156,B_154)))
      | ~ v1_funct_2(F_158,D_156,B_154)
      | ~ v1_funct_1(F_158)
      | ~ m1_subset_1(E_157,k1_zfmisc_1(k2_zfmisc_1(C_155,B_154)))
      | ~ v1_funct_2(E_157,C_155,B_154)
      | ~ v1_funct_1(E_157)
      | ~ m1_subset_1(D_156,k1_zfmisc_1(A_153))
      | v1_xboole_0(D_156)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(A_153))
      | v1_xboole_0(C_155)
      | v1_xboole_0(B_154)
      | v1_xboole_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2590,plain,(
    ! [A_689,D_690,B_691,E_694,F_692,C_693] :
      ( k2_partfun1(k4_subset_1(A_689,C_693,D_690),B_691,k1_tmap_1(A_689,B_691,C_693,D_690,E_694,F_692),C_693) = E_694
      | ~ m1_subset_1(k1_tmap_1(A_689,B_691,C_693,D_690,E_694,F_692),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_689,C_693,D_690),B_691)))
      | ~ v1_funct_2(k1_tmap_1(A_689,B_691,C_693,D_690,E_694,F_692),k4_subset_1(A_689,C_693,D_690),B_691)
      | ~ v1_funct_1(k1_tmap_1(A_689,B_691,C_693,D_690,E_694,F_692))
      | k2_partfun1(D_690,B_691,F_692,k9_subset_1(A_689,C_693,D_690)) != k2_partfun1(C_693,B_691,E_694,k9_subset_1(A_689,C_693,D_690))
      | ~ m1_subset_1(F_692,k1_zfmisc_1(k2_zfmisc_1(D_690,B_691)))
      | ~ v1_funct_2(F_692,D_690,B_691)
      | ~ v1_funct_1(F_692)
      | ~ m1_subset_1(E_694,k1_zfmisc_1(k2_zfmisc_1(C_693,B_691)))
      | ~ v1_funct_2(E_694,C_693,B_691)
      | ~ v1_funct_1(E_694)
      | ~ m1_subset_1(D_690,k1_zfmisc_1(A_689))
      | v1_xboole_0(D_690)
      | ~ m1_subset_1(C_693,k1_zfmisc_1(A_689))
      | v1_xboole_0(C_693)
      | v1_xboole_0(B_691)
      | v1_xboole_0(A_689) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3237,plain,(
    ! [F_799,D_803,E_800,B_801,A_802,C_798] :
      ( k2_partfun1(k4_subset_1(A_802,C_798,D_803),B_801,k1_tmap_1(A_802,B_801,C_798,D_803,E_800,F_799),C_798) = E_800
      | ~ v1_funct_2(k1_tmap_1(A_802,B_801,C_798,D_803,E_800,F_799),k4_subset_1(A_802,C_798,D_803),B_801)
      | ~ v1_funct_1(k1_tmap_1(A_802,B_801,C_798,D_803,E_800,F_799))
      | k2_partfun1(D_803,B_801,F_799,k9_subset_1(A_802,C_798,D_803)) != k2_partfun1(C_798,B_801,E_800,k9_subset_1(A_802,C_798,D_803))
      | ~ m1_subset_1(F_799,k1_zfmisc_1(k2_zfmisc_1(D_803,B_801)))
      | ~ v1_funct_2(F_799,D_803,B_801)
      | ~ v1_funct_1(F_799)
      | ~ m1_subset_1(E_800,k1_zfmisc_1(k2_zfmisc_1(C_798,B_801)))
      | ~ v1_funct_2(E_800,C_798,B_801)
      | ~ v1_funct_1(E_800)
      | ~ m1_subset_1(D_803,k1_zfmisc_1(A_802))
      | v1_xboole_0(D_803)
      | ~ m1_subset_1(C_798,k1_zfmisc_1(A_802))
      | v1_xboole_0(C_798)
      | v1_xboole_0(B_801)
      | v1_xboole_0(A_802) ) ),
    inference(resolution,[status(thm)],[c_38,c_2590])).

tff(c_3302,plain,(
    ! [E_814,B_815,A_816,F_813,C_812,D_817] :
      ( k2_partfun1(k4_subset_1(A_816,C_812,D_817),B_815,k1_tmap_1(A_816,B_815,C_812,D_817,E_814,F_813),C_812) = E_814
      | ~ v1_funct_1(k1_tmap_1(A_816,B_815,C_812,D_817,E_814,F_813))
      | k2_partfun1(D_817,B_815,F_813,k9_subset_1(A_816,C_812,D_817)) != k2_partfun1(C_812,B_815,E_814,k9_subset_1(A_816,C_812,D_817))
      | ~ m1_subset_1(F_813,k1_zfmisc_1(k2_zfmisc_1(D_817,B_815)))
      | ~ v1_funct_2(F_813,D_817,B_815)
      | ~ v1_funct_1(F_813)
      | ~ m1_subset_1(E_814,k1_zfmisc_1(k2_zfmisc_1(C_812,B_815)))
      | ~ v1_funct_2(E_814,C_812,B_815)
      | ~ v1_funct_1(E_814)
      | ~ m1_subset_1(D_817,k1_zfmisc_1(A_816))
      | v1_xboole_0(D_817)
      | ~ m1_subset_1(C_812,k1_zfmisc_1(A_816))
      | v1_xboole_0(C_812)
      | v1_xboole_0(B_815)
      | v1_xboole_0(A_816) ) ),
    inference(resolution,[status(thm)],[c_40,c_3237])).

tff(c_3306,plain,(
    ! [A_816,C_812,E_814] :
      ( k2_partfun1(k4_subset_1(A_816,C_812,'#skF_6'),'#skF_4',k1_tmap_1(A_816,'#skF_4',C_812,'#skF_6',E_814,'#skF_8'),C_812) = E_814
      | ~ v1_funct_1(k1_tmap_1(A_816,'#skF_4',C_812,'#skF_6',E_814,'#skF_8'))
      | k2_partfun1(C_812,'#skF_4',E_814,k9_subset_1(A_816,C_812,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_816,C_812,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_814,k1_zfmisc_1(k2_zfmisc_1(C_812,'#skF_4')))
      | ~ v1_funct_2(E_814,C_812,'#skF_4')
      | ~ v1_funct_1(E_814)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_816))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_812,k1_zfmisc_1(A_816))
      | v1_xboole_0(C_812)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_816) ) ),
    inference(resolution,[status(thm)],[c_46,c_3302])).

tff(c_3312,plain,(
    ! [A_816,C_812,E_814] :
      ( k2_partfun1(k4_subset_1(A_816,C_812,'#skF_6'),'#skF_4',k1_tmap_1(A_816,'#skF_4',C_812,'#skF_6',E_814,'#skF_8'),C_812) = E_814
      | ~ v1_funct_1(k1_tmap_1(A_816,'#skF_4',C_812,'#skF_6',E_814,'#skF_8'))
      | k2_partfun1(C_812,'#skF_4',E_814,k9_subset_1(A_816,C_812,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_816,C_812,'#skF_6'))
      | ~ m1_subset_1(E_814,k1_zfmisc_1(k2_zfmisc_1(C_812,'#skF_4')))
      | ~ v1_funct_2(E_814,C_812,'#skF_4')
      | ~ v1_funct_1(E_814)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_816))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_812,k1_zfmisc_1(A_816))
      | v1_xboole_0(C_812)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_816) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2199,c_3306])).

tff(c_3318,plain,(
    ! [A_818,C_819,E_820] :
      ( k2_partfun1(k4_subset_1(A_818,C_819,'#skF_6'),'#skF_4',k1_tmap_1(A_818,'#skF_4',C_819,'#skF_6',E_820,'#skF_8'),C_819) = E_820
      | ~ v1_funct_1(k1_tmap_1(A_818,'#skF_4',C_819,'#skF_6',E_820,'#skF_8'))
      | k2_partfun1(C_819,'#skF_4',E_820,k9_subset_1(A_818,C_819,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_818,C_819,'#skF_6'))
      | ~ m1_subset_1(E_820,k1_zfmisc_1(k2_zfmisc_1(C_819,'#skF_4')))
      | ~ v1_funct_2(E_820,C_819,'#skF_4')
      | ~ v1_funct_1(E_820)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_818))
      | ~ m1_subset_1(C_819,k1_zfmisc_1(A_818))
      | v1_xboole_0(C_819)
      | v1_xboole_0(A_818) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_3312])).

tff(c_3325,plain,(
    ! [A_818] :
      ( k2_partfun1(k4_subset_1(A_818,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_818,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_818,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_818,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_818,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_818))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_818))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_818) ) ),
    inference(resolution,[status(thm)],[c_52,c_3318])).

tff(c_3335,plain,(
    ! [A_818] :
      ( k2_partfun1(k4_subset_1(A_818,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_818,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_818,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_818,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_818,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_818))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_818))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_818) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2202,c_3325])).

tff(c_3380,plain,(
    ! [A_829] :
      ( k2_partfun1(k4_subset_1(A_829,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_829,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_829,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_829,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_829,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_829))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_829))
      | v1_xboole_0(A_829) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3335])).

tff(c_646,plain,(
    ! [A_332,B_333] :
      ( k3_xboole_0(A_332,B_333) = k1_xboole_0
      | ~ r1_subset_1(A_332,B_333)
      | v1_xboole_0(B_333)
      | v1_xboole_0(A_332) ) ),
    inference(resolution,[status(thm)],[c_499,c_6])).

tff(c_649,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_646])).

tff(c_652,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_62,c_649])).

tff(c_568,plain,(
    ! [A_321,B_322,C_323] :
      ( k9_subset_1(A_321,B_322,C_323) = k3_xboole_0(B_322,C_323)
      | ~ m1_subset_1(C_323,k1_zfmisc_1(A_321)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_579,plain,(
    ! [B_322] : k9_subset_1('#skF_3',B_322,'#skF_6') = k3_xboole_0(B_322,'#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_568])).

tff(c_795,plain,(
    ! [C_353,F_354,B_356,A_357,E_355,D_358] :
      ( v1_funct_1(k1_tmap_1(A_357,B_356,C_353,D_358,E_355,F_354))
      | ~ m1_subset_1(F_354,k1_zfmisc_1(k2_zfmisc_1(D_358,B_356)))
      | ~ v1_funct_2(F_354,D_358,B_356)
      | ~ v1_funct_1(F_354)
      | ~ m1_subset_1(E_355,k1_zfmisc_1(k2_zfmisc_1(C_353,B_356)))
      | ~ v1_funct_2(E_355,C_353,B_356)
      | ~ v1_funct_1(E_355)
      | ~ m1_subset_1(D_358,k1_zfmisc_1(A_357))
      | v1_xboole_0(D_358)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(A_357))
      | v1_xboole_0(C_353)
      | v1_xboole_0(B_356)
      | v1_xboole_0(A_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_797,plain,(
    ! [A_357,C_353,E_355] :
      ( v1_funct_1(k1_tmap_1(A_357,'#skF_4',C_353,'#skF_6',E_355,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_355,k1_zfmisc_1(k2_zfmisc_1(C_353,'#skF_4')))
      | ~ v1_funct_2(E_355,C_353,'#skF_4')
      | ~ v1_funct_1(E_355)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_357))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_353,k1_zfmisc_1(A_357))
      | v1_xboole_0(C_353)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_357) ) ),
    inference(resolution,[status(thm)],[c_46,c_795])).

tff(c_802,plain,(
    ! [A_357,C_353,E_355] :
      ( v1_funct_1(k1_tmap_1(A_357,'#skF_4',C_353,'#skF_6',E_355,'#skF_8'))
      | ~ m1_subset_1(E_355,k1_zfmisc_1(k2_zfmisc_1(C_353,'#skF_4')))
      | ~ v1_funct_2(E_355,C_353,'#skF_4')
      | ~ v1_funct_1(E_355)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_357))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_353,k1_zfmisc_1(A_357))
      | v1_xboole_0(C_353)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_357) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_797])).

tff(c_893,plain,(
    ! [A_379,C_380,E_381] :
      ( v1_funct_1(k1_tmap_1(A_379,'#skF_4',C_380,'#skF_6',E_381,'#skF_8'))
      | ~ m1_subset_1(E_381,k1_zfmisc_1(k2_zfmisc_1(C_380,'#skF_4')))
      | ~ v1_funct_2(E_381,C_380,'#skF_4')
      | ~ v1_funct_1(E_381)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_379))
      | ~ m1_subset_1(C_380,k1_zfmisc_1(A_379))
      | v1_xboole_0(C_380)
      | v1_xboole_0(A_379) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_802])).

tff(c_897,plain,(
    ! [A_379] :
      ( v1_funct_1(k1_tmap_1(A_379,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_379))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_379))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_379) ) ),
    inference(resolution,[status(thm)],[c_52,c_893])).

tff(c_904,plain,(
    ! [A_379] :
      ( v1_funct_1(k1_tmap_1(A_379,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_379))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_379))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_379) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_897])).

tff(c_1091,plain,(
    ! [A_427] :
      ( v1_funct_1(k1_tmap_1(A_427,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_427))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_427))
      | v1_xboole_0(A_427) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_904])).

tff(c_1094,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1091])).

tff(c_1097,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1094])).

tff(c_1098,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1097])).

tff(c_752,plain,(
    ! [A_347,B_348,C_349,D_350] :
      ( k2_partfun1(A_347,B_348,C_349,D_350) = k7_relat_1(C_349,D_350)
      | ~ m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(A_347,B_348)))
      | ~ v1_funct_1(C_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_756,plain,(
    ! [D_350] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_350) = k7_relat_1('#skF_7',D_350)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_52,c_752])).

tff(c_762,plain,(
    ! [D_350] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_350) = k7_relat_1('#skF_7',D_350) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_756])).

tff(c_754,plain,(
    ! [D_350] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_350) = k7_relat_1('#skF_8',D_350)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_46,c_752])).

tff(c_759,plain,(
    ! [D_350] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_350) = k7_relat_1('#skF_8',D_350) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_754])).

tff(c_1135,plain,(
    ! [C_439,D_436,F_438,E_440,B_437,A_435] :
      ( k2_partfun1(k4_subset_1(A_435,C_439,D_436),B_437,k1_tmap_1(A_435,B_437,C_439,D_436,E_440,F_438),D_436) = F_438
      | ~ m1_subset_1(k1_tmap_1(A_435,B_437,C_439,D_436,E_440,F_438),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_435,C_439,D_436),B_437)))
      | ~ v1_funct_2(k1_tmap_1(A_435,B_437,C_439,D_436,E_440,F_438),k4_subset_1(A_435,C_439,D_436),B_437)
      | ~ v1_funct_1(k1_tmap_1(A_435,B_437,C_439,D_436,E_440,F_438))
      | k2_partfun1(D_436,B_437,F_438,k9_subset_1(A_435,C_439,D_436)) != k2_partfun1(C_439,B_437,E_440,k9_subset_1(A_435,C_439,D_436))
      | ~ m1_subset_1(F_438,k1_zfmisc_1(k2_zfmisc_1(D_436,B_437)))
      | ~ v1_funct_2(F_438,D_436,B_437)
      | ~ v1_funct_1(F_438)
      | ~ m1_subset_1(E_440,k1_zfmisc_1(k2_zfmisc_1(C_439,B_437)))
      | ~ v1_funct_2(E_440,C_439,B_437)
      | ~ v1_funct_1(E_440)
      | ~ m1_subset_1(D_436,k1_zfmisc_1(A_435))
      | v1_xboole_0(D_436)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(A_435))
      | v1_xboole_0(C_439)
      | v1_xboole_0(B_437)
      | v1_xboole_0(A_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1790,plain,(
    ! [A_540,C_536,F_537,E_538,D_541,B_539] :
      ( k2_partfun1(k4_subset_1(A_540,C_536,D_541),B_539,k1_tmap_1(A_540,B_539,C_536,D_541,E_538,F_537),D_541) = F_537
      | ~ v1_funct_2(k1_tmap_1(A_540,B_539,C_536,D_541,E_538,F_537),k4_subset_1(A_540,C_536,D_541),B_539)
      | ~ v1_funct_1(k1_tmap_1(A_540,B_539,C_536,D_541,E_538,F_537))
      | k2_partfun1(D_541,B_539,F_537,k9_subset_1(A_540,C_536,D_541)) != k2_partfun1(C_536,B_539,E_538,k9_subset_1(A_540,C_536,D_541))
      | ~ m1_subset_1(F_537,k1_zfmisc_1(k2_zfmisc_1(D_541,B_539)))
      | ~ v1_funct_2(F_537,D_541,B_539)
      | ~ v1_funct_1(F_537)
      | ~ m1_subset_1(E_538,k1_zfmisc_1(k2_zfmisc_1(C_536,B_539)))
      | ~ v1_funct_2(E_538,C_536,B_539)
      | ~ v1_funct_1(E_538)
      | ~ m1_subset_1(D_541,k1_zfmisc_1(A_540))
      | v1_xboole_0(D_541)
      | ~ m1_subset_1(C_536,k1_zfmisc_1(A_540))
      | v1_xboole_0(C_536)
      | v1_xboole_0(B_539)
      | v1_xboole_0(A_540) ) ),
    inference(resolution,[status(thm)],[c_38,c_1135])).

tff(c_1844,plain,(
    ! [D_555,C_550,E_552,B_553,F_551,A_554] :
      ( k2_partfun1(k4_subset_1(A_554,C_550,D_555),B_553,k1_tmap_1(A_554,B_553,C_550,D_555,E_552,F_551),D_555) = F_551
      | ~ v1_funct_1(k1_tmap_1(A_554,B_553,C_550,D_555,E_552,F_551))
      | k2_partfun1(D_555,B_553,F_551,k9_subset_1(A_554,C_550,D_555)) != k2_partfun1(C_550,B_553,E_552,k9_subset_1(A_554,C_550,D_555))
      | ~ m1_subset_1(F_551,k1_zfmisc_1(k2_zfmisc_1(D_555,B_553)))
      | ~ v1_funct_2(F_551,D_555,B_553)
      | ~ v1_funct_1(F_551)
      | ~ m1_subset_1(E_552,k1_zfmisc_1(k2_zfmisc_1(C_550,B_553)))
      | ~ v1_funct_2(E_552,C_550,B_553)
      | ~ v1_funct_1(E_552)
      | ~ m1_subset_1(D_555,k1_zfmisc_1(A_554))
      | v1_xboole_0(D_555)
      | ~ m1_subset_1(C_550,k1_zfmisc_1(A_554))
      | v1_xboole_0(C_550)
      | v1_xboole_0(B_553)
      | v1_xboole_0(A_554) ) ),
    inference(resolution,[status(thm)],[c_40,c_1790])).

tff(c_1848,plain,(
    ! [A_554,C_550,E_552] :
      ( k2_partfun1(k4_subset_1(A_554,C_550,'#skF_6'),'#skF_4',k1_tmap_1(A_554,'#skF_4',C_550,'#skF_6',E_552,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_554,'#skF_4',C_550,'#skF_6',E_552,'#skF_8'))
      | k2_partfun1(C_550,'#skF_4',E_552,k9_subset_1(A_554,C_550,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_554,C_550,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_552,k1_zfmisc_1(k2_zfmisc_1(C_550,'#skF_4')))
      | ~ v1_funct_2(E_552,C_550,'#skF_4')
      | ~ v1_funct_1(E_552)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_554))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_550,k1_zfmisc_1(A_554))
      | v1_xboole_0(C_550)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_554) ) ),
    inference(resolution,[status(thm)],[c_46,c_1844])).

tff(c_1854,plain,(
    ! [A_554,C_550,E_552] :
      ( k2_partfun1(k4_subset_1(A_554,C_550,'#skF_6'),'#skF_4',k1_tmap_1(A_554,'#skF_4',C_550,'#skF_6',E_552,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_554,'#skF_4',C_550,'#skF_6',E_552,'#skF_8'))
      | k2_partfun1(C_550,'#skF_4',E_552,k9_subset_1(A_554,C_550,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_554,C_550,'#skF_6'))
      | ~ m1_subset_1(E_552,k1_zfmisc_1(k2_zfmisc_1(C_550,'#skF_4')))
      | ~ v1_funct_2(E_552,C_550,'#skF_4')
      | ~ v1_funct_1(E_552)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_554))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_550,k1_zfmisc_1(A_554))
      | v1_xboole_0(C_550)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_554) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_759,c_1848])).

tff(c_1860,plain,(
    ! [A_556,C_557,E_558] :
      ( k2_partfun1(k4_subset_1(A_556,C_557,'#skF_6'),'#skF_4',k1_tmap_1(A_556,'#skF_4',C_557,'#skF_6',E_558,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_556,'#skF_4',C_557,'#skF_6',E_558,'#skF_8'))
      | k2_partfun1(C_557,'#skF_4',E_558,k9_subset_1(A_556,C_557,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_556,C_557,'#skF_6'))
      | ~ m1_subset_1(E_558,k1_zfmisc_1(k2_zfmisc_1(C_557,'#skF_4')))
      | ~ v1_funct_2(E_558,C_557,'#skF_4')
      | ~ v1_funct_1(E_558)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_556))
      | ~ m1_subset_1(C_557,k1_zfmisc_1(A_556))
      | v1_xboole_0(C_557)
      | v1_xboole_0(A_556) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_1854])).

tff(c_1867,plain,(
    ! [A_556] :
      ( k2_partfun1(k4_subset_1(A_556,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_556,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_556,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_556,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_556,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_556))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_556))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_556) ) ),
    inference(resolution,[status(thm)],[c_52,c_1860])).

tff(c_1877,plain,(
    ! [A_556] :
      ( k2_partfun1(k4_subset_1(A_556,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_556,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_556,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_556,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_556,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_556))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_556))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_556) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_762,c_1867])).

tff(c_1922,plain,(
    ! [A_567] :
      ( k2_partfun1(k4_subset_1(A_567,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_567,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_567,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_567,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_567,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_567))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_567))
      | v1_xboole_0(A_567) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1877])).

tff(c_93,plain,(
    ! [A_226,B_227] :
      ( r2_hidden('#skF_2'(A_226,B_227),B_227)
      | r1_xboole_0(A_226,B_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_97,plain,(
    ! [B_227,A_226] :
      ( ~ v1_xboole_0(B_227)
      | r1_xboole_0(A_226,B_227) ) ),
    inference(resolution,[status(thm)],[c_93,c_2])).

tff(c_161,plain,(
    ! [B_245,A_246] :
      ( k7_relat_1(B_245,A_246) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_245),A_246)
      | ~ v1_relat_1(B_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_182,plain,(
    ! [B_247,B_248] :
      ( k7_relat_1(B_247,B_248) = k1_xboole_0
      | ~ v1_relat_1(B_247)
      | ~ v1_xboole_0(B_248) ) ),
    inference(resolution,[status(thm)],[c_97,c_161])).

tff(c_201,plain,(
    ! [B_251] :
      ( k7_relat_1('#skF_7',B_251) = k1_xboole_0
      | ~ v1_xboole_0(B_251) ) ),
    inference(resolution,[status(thm)],[c_91,c_182])).

tff(c_205,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_201])).

tff(c_357,plain,(
    ! [A_277,B_278,C_279,D_280] :
      ( k2_partfun1(A_277,B_278,C_279,D_280) = k7_relat_1(C_279,D_280)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_277,B_278)))
      | ~ v1_funct_1(C_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_361,plain,(
    ! [D_280] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_280) = k7_relat_1('#skF_7',D_280)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_52,c_357])).

tff(c_367,plain,(
    ! [D_280] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_280) = k7_relat_1('#skF_7',D_280) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_361])).

tff(c_210,plain,(
    ! [B_252] :
      ( k7_relat_1('#skF_8',B_252) = k1_xboole_0
      | ~ v1_xboole_0(B_252) ) ),
    inference(resolution,[status(thm)],[c_90,c_182])).

tff(c_214,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_210])).

tff(c_359,plain,(
    ! [D_280] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_280) = k7_relat_1('#skF_8',D_280)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_46,c_357])).

tff(c_364,plain,(
    ! [D_280] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_280) = k7_relat_1('#skF_8',D_280) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_359])).

tff(c_153,plain,(
    ! [A_243,B_244] :
      ( r1_xboole_0(A_243,B_244)
      | ~ r1_subset_1(A_243,B_244)
      | v1_xboole_0(B_244)
      | v1_xboole_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_317,plain,(
    ! [A_270,B_271] :
      ( k3_xboole_0(A_270,B_271) = k1_xboole_0
      | ~ r1_subset_1(A_270,B_271)
      | v1_xboole_0(B_271)
      | v1_xboole_0(A_270) ) ),
    inference(resolution,[status(thm)],[c_153,c_6])).

tff(c_320,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_317])).

tff(c_323,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_62,c_320])).

tff(c_267,plain,(
    ! [A_263,B_264,C_265] :
      ( k9_subset_1(A_263,B_264,C_265) = k3_xboole_0(B_264,C_265)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(A_263)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_278,plain,(
    ! [B_264] : k9_subset_1('#skF_3',B_264,'#skF_6') = k3_xboole_0(B_264,'#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_267])).

tff(c_44,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_92,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_280,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k3_xboole_0('#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_278,c_92])).

tff(c_397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_367,c_214,c_364,c_323,c_323,c_280])).

tff(c_398,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_526,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_398])).

tff(c_1933,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1922,c_526])).

tff(c_1947,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_525,c_652,c_516,c_652,c_579,c_579,c_1098,c_1933])).

tff(c_1949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1947])).

tff(c_1950,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_398])).

tff(c_3389,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3380,c_1950])).

tff(c_3400,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_525,c_2060,c_516,c_2060,c_2015,c_2015,c_2740,c_3389])).

tff(c_3402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n009.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 11:20:41 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.47/3.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.47/3.22  
% 9.47/3.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.47/3.23  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 9.47/3.23  
% 9.47/3.23  %Foreground sorts:
% 9.47/3.23  
% 9.47/3.23  
% 9.47/3.23  %Background operators:
% 9.47/3.23  
% 9.47/3.23  
% 9.47/3.23  %Foreground operators:
% 9.47/3.23  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 9.47/3.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.47/3.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.47/3.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.47/3.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.47/3.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.47/3.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.47/3.23  tff('#skF_7', type, '#skF_7': $i).
% 9.47/3.23  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.47/3.23  tff('#skF_5', type, '#skF_5': $i).
% 9.47/3.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.47/3.23  tff('#skF_6', type, '#skF_6': $i).
% 9.47/3.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.47/3.23  tff('#skF_3', type, '#skF_3': $i).
% 9.47/3.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.47/3.23  tff('#skF_8', type, '#skF_8': $i).
% 9.47/3.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.47/3.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.47/3.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.47/3.23  tff('#skF_4', type, '#skF_4': $i).
% 9.47/3.23  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.47/3.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.47/3.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.47/3.23  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.47/3.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.47/3.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.47/3.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.47/3.23  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.47/3.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.47/3.23  
% 9.47/3.25  tff(f_208, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 9.47/3.25  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.47/3.25  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.47/3.25  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.47/3.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.47/3.25  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 9.47/3.25  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 9.47/3.25  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.47/3.25  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 9.47/3.25  tff(f_166, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 9.47/3.25  tff(f_84, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.47/3.25  tff(f_132, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 9.47/3.25  tff(c_70, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.25  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.25  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.25  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.47/3.25  tff(c_46, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.25  tff(c_83, plain, (![C_223, A_224, B_225]: (v1_relat_1(C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.47/3.25  tff(c_90, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_46, c_83])).
% 9.47/3.25  tff(c_400, plain, (![A_285, B_286]: (r2_hidden('#skF_2'(A_285, B_286), B_286) | r1_xboole_0(A_285, B_286))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.47/3.25  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.47/3.25  tff(c_404, plain, (![B_286, A_285]: (~v1_xboole_0(B_286) | r1_xboole_0(A_285, B_286))), inference(resolution, [status(thm)], [c_400, c_2])).
% 9.47/3.25  tff(c_472, plain, (![B_304, A_305]: (k7_relat_1(B_304, A_305)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_304), A_305) | ~v1_relat_1(B_304))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.47/3.25  tff(c_492, plain, (![B_306, B_307]: (k7_relat_1(B_306, B_307)=k1_xboole_0 | ~v1_relat_1(B_306) | ~v1_xboole_0(B_307))), inference(resolution, [status(thm)], [c_404, c_472])).
% 9.47/3.25  tff(c_521, plain, (![B_311]: (k7_relat_1('#skF_8', B_311)=k1_xboole_0 | ~v1_xboole_0(B_311))), inference(resolution, [status(thm)], [c_90, c_492])).
% 9.47/3.25  tff(c_525, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_521])).
% 9.47/3.25  tff(c_66, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.25  tff(c_62, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.25  tff(c_58, plain, (r1_subset_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.25  tff(c_499, plain, (![A_308, B_309]: (r1_xboole_0(A_308, B_309) | ~r1_subset_1(A_308, B_309) | v1_xboole_0(B_309) | v1_xboole_0(A_308))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.47/3.25  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.47/3.25  tff(c_2054, plain, (![A_585, B_586]: (k3_xboole_0(A_585, B_586)=k1_xboole_0 | ~r1_subset_1(A_585, B_586) | v1_xboole_0(B_586) | v1_xboole_0(A_585))), inference(resolution, [status(thm)], [c_499, c_6])).
% 9.47/3.25  tff(c_2057, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_2054])).
% 9.47/3.25  tff(c_2060, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_62, c_2057])).
% 9.47/3.25  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.25  tff(c_91, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_52, c_83])).
% 9.47/3.25  tff(c_512, plain, (![B_310]: (k7_relat_1('#skF_7', B_310)=k1_xboole_0 | ~v1_xboole_0(B_310))), inference(resolution, [status(thm)], [c_91, c_492])).
% 9.47/3.25  tff(c_516, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_512])).
% 9.47/3.25  tff(c_2004, plain, (![A_578, B_579, C_580]: (k9_subset_1(A_578, B_579, C_580)=k3_xboole_0(B_579, C_580) | ~m1_subset_1(C_580, k1_zfmisc_1(A_578)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.47/3.25  tff(c_2015, plain, (![B_579]: (k9_subset_1('#skF_3', B_579, '#skF_6')=k3_xboole_0(B_579, '#skF_6'))), inference(resolution, [status(thm)], [c_60, c_2004])).
% 9.47/3.25  tff(c_56, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.25  tff(c_54, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.25  tff(c_68, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.25  tff(c_50, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.25  tff(c_48, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.25  tff(c_2293, plain, (![A_625, B_624, F_622, D_626, C_621, E_623]: (v1_funct_1(k1_tmap_1(A_625, B_624, C_621, D_626, E_623, F_622)) | ~m1_subset_1(F_622, k1_zfmisc_1(k2_zfmisc_1(D_626, B_624))) | ~v1_funct_2(F_622, D_626, B_624) | ~v1_funct_1(F_622) | ~m1_subset_1(E_623, k1_zfmisc_1(k2_zfmisc_1(C_621, B_624))) | ~v1_funct_2(E_623, C_621, B_624) | ~v1_funct_1(E_623) | ~m1_subset_1(D_626, k1_zfmisc_1(A_625)) | v1_xboole_0(D_626) | ~m1_subset_1(C_621, k1_zfmisc_1(A_625)) | v1_xboole_0(C_621) | v1_xboole_0(B_624) | v1_xboole_0(A_625))), inference(cnfTransformation, [status(thm)], [f_166])).
% 9.47/3.25  tff(c_2295, plain, (![A_625, C_621, E_623]: (v1_funct_1(k1_tmap_1(A_625, '#skF_4', C_621, '#skF_6', E_623, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_623, k1_zfmisc_1(k2_zfmisc_1(C_621, '#skF_4'))) | ~v1_funct_2(E_623, C_621, '#skF_4') | ~v1_funct_1(E_623) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_625)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_621, k1_zfmisc_1(A_625)) | v1_xboole_0(C_621) | v1_xboole_0('#skF_4') | v1_xboole_0(A_625))), inference(resolution, [status(thm)], [c_46, c_2293])).
% 9.47/3.25  tff(c_2300, plain, (![A_625, C_621, E_623]: (v1_funct_1(k1_tmap_1(A_625, '#skF_4', C_621, '#skF_6', E_623, '#skF_8')) | ~m1_subset_1(E_623, k1_zfmisc_1(k2_zfmisc_1(C_621, '#skF_4'))) | ~v1_funct_2(E_623, C_621, '#skF_4') | ~v1_funct_1(E_623) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_625)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_621, k1_zfmisc_1(A_625)) | v1_xboole_0(C_621) | v1_xboole_0('#skF_4') | v1_xboole_0(A_625))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2295])).
% 9.47/3.25  tff(c_2640, plain, (![A_700, C_701, E_702]: (v1_funct_1(k1_tmap_1(A_700, '#skF_4', C_701, '#skF_6', E_702, '#skF_8')) | ~m1_subset_1(E_702, k1_zfmisc_1(k2_zfmisc_1(C_701, '#skF_4'))) | ~v1_funct_2(E_702, C_701, '#skF_4') | ~v1_funct_1(E_702) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_700)) | ~m1_subset_1(C_701, k1_zfmisc_1(A_700)) | v1_xboole_0(C_701) | v1_xboole_0(A_700))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_2300])).
% 9.47/3.25  tff(c_2647, plain, (![A_700]: (v1_funct_1(k1_tmap_1(A_700, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_700)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_700)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_700))), inference(resolution, [status(thm)], [c_52, c_2640])).
% 9.47/3.25  tff(c_2657, plain, (![A_700]: (v1_funct_1(k1_tmap_1(A_700, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_700)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_700)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_700))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_2647])).
% 9.47/3.25  tff(c_2733, plain, (![A_725]: (v1_funct_1(k1_tmap_1(A_725, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_725)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_725)) | v1_xboole_0(A_725))), inference(negUnitSimplification, [status(thm)], [c_66, c_2657])).
% 9.47/3.25  tff(c_2736, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_2733])).
% 9.47/3.25  tff(c_2739, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2736])).
% 9.47/3.25  tff(c_2740, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_70, c_2739])).
% 9.47/3.25  tff(c_2192, plain, (![A_605, B_606, C_607, D_608]: (k2_partfun1(A_605, B_606, C_607, D_608)=k7_relat_1(C_607, D_608) | ~m1_subset_1(C_607, k1_zfmisc_1(k2_zfmisc_1(A_605, B_606))) | ~v1_funct_1(C_607))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.47/3.25  tff(c_2196, plain, (![D_608]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_608)=k7_relat_1('#skF_7', D_608) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_52, c_2192])).
% 9.47/3.25  tff(c_2202, plain, (![D_608]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_608)=k7_relat_1('#skF_7', D_608))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2196])).
% 9.47/3.25  tff(c_2194, plain, (![D_608]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_608)=k7_relat_1('#skF_8', D_608) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_46, c_2192])).
% 9.47/3.25  tff(c_2199, plain, (![D_608]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_608)=k7_relat_1('#skF_8', D_608))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2194])).
% 9.47/3.25  tff(c_40, plain, (![F_158, C_155, D_156, E_157, A_153, B_154]: (v1_funct_2(k1_tmap_1(A_153, B_154, C_155, D_156, E_157, F_158), k4_subset_1(A_153, C_155, D_156), B_154) | ~m1_subset_1(F_158, k1_zfmisc_1(k2_zfmisc_1(D_156, B_154))) | ~v1_funct_2(F_158, D_156, B_154) | ~v1_funct_1(F_158) | ~m1_subset_1(E_157, k1_zfmisc_1(k2_zfmisc_1(C_155, B_154))) | ~v1_funct_2(E_157, C_155, B_154) | ~v1_funct_1(E_157) | ~m1_subset_1(D_156, k1_zfmisc_1(A_153)) | v1_xboole_0(D_156) | ~m1_subset_1(C_155, k1_zfmisc_1(A_153)) | v1_xboole_0(C_155) | v1_xboole_0(B_154) | v1_xboole_0(A_153))), inference(cnfTransformation, [status(thm)], [f_166])).
% 9.47/3.25  tff(c_38, plain, (![F_158, C_155, D_156, E_157, A_153, B_154]: (m1_subset_1(k1_tmap_1(A_153, B_154, C_155, D_156, E_157, F_158), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_153, C_155, D_156), B_154))) | ~m1_subset_1(F_158, k1_zfmisc_1(k2_zfmisc_1(D_156, B_154))) | ~v1_funct_2(F_158, D_156, B_154) | ~v1_funct_1(F_158) | ~m1_subset_1(E_157, k1_zfmisc_1(k2_zfmisc_1(C_155, B_154))) | ~v1_funct_2(E_157, C_155, B_154) | ~v1_funct_1(E_157) | ~m1_subset_1(D_156, k1_zfmisc_1(A_153)) | v1_xboole_0(D_156) | ~m1_subset_1(C_155, k1_zfmisc_1(A_153)) | v1_xboole_0(C_155) | v1_xboole_0(B_154) | v1_xboole_0(A_153))), inference(cnfTransformation, [status(thm)], [f_166])).
% 9.47/3.25  tff(c_2590, plain, (![A_689, D_690, B_691, E_694, F_692, C_693]: (k2_partfun1(k4_subset_1(A_689, C_693, D_690), B_691, k1_tmap_1(A_689, B_691, C_693, D_690, E_694, F_692), C_693)=E_694 | ~m1_subset_1(k1_tmap_1(A_689, B_691, C_693, D_690, E_694, F_692), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_689, C_693, D_690), B_691))) | ~v1_funct_2(k1_tmap_1(A_689, B_691, C_693, D_690, E_694, F_692), k4_subset_1(A_689, C_693, D_690), B_691) | ~v1_funct_1(k1_tmap_1(A_689, B_691, C_693, D_690, E_694, F_692)) | k2_partfun1(D_690, B_691, F_692, k9_subset_1(A_689, C_693, D_690))!=k2_partfun1(C_693, B_691, E_694, k9_subset_1(A_689, C_693, D_690)) | ~m1_subset_1(F_692, k1_zfmisc_1(k2_zfmisc_1(D_690, B_691))) | ~v1_funct_2(F_692, D_690, B_691) | ~v1_funct_1(F_692) | ~m1_subset_1(E_694, k1_zfmisc_1(k2_zfmisc_1(C_693, B_691))) | ~v1_funct_2(E_694, C_693, B_691) | ~v1_funct_1(E_694) | ~m1_subset_1(D_690, k1_zfmisc_1(A_689)) | v1_xboole_0(D_690) | ~m1_subset_1(C_693, k1_zfmisc_1(A_689)) | v1_xboole_0(C_693) | v1_xboole_0(B_691) | v1_xboole_0(A_689))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.47/3.25  tff(c_3237, plain, (![F_799, D_803, E_800, B_801, A_802, C_798]: (k2_partfun1(k4_subset_1(A_802, C_798, D_803), B_801, k1_tmap_1(A_802, B_801, C_798, D_803, E_800, F_799), C_798)=E_800 | ~v1_funct_2(k1_tmap_1(A_802, B_801, C_798, D_803, E_800, F_799), k4_subset_1(A_802, C_798, D_803), B_801) | ~v1_funct_1(k1_tmap_1(A_802, B_801, C_798, D_803, E_800, F_799)) | k2_partfun1(D_803, B_801, F_799, k9_subset_1(A_802, C_798, D_803))!=k2_partfun1(C_798, B_801, E_800, k9_subset_1(A_802, C_798, D_803)) | ~m1_subset_1(F_799, k1_zfmisc_1(k2_zfmisc_1(D_803, B_801))) | ~v1_funct_2(F_799, D_803, B_801) | ~v1_funct_1(F_799) | ~m1_subset_1(E_800, k1_zfmisc_1(k2_zfmisc_1(C_798, B_801))) | ~v1_funct_2(E_800, C_798, B_801) | ~v1_funct_1(E_800) | ~m1_subset_1(D_803, k1_zfmisc_1(A_802)) | v1_xboole_0(D_803) | ~m1_subset_1(C_798, k1_zfmisc_1(A_802)) | v1_xboole_0(C_798) | v1_xboole_0(B_801) | v1_xboole_0(A_802))), inference(resolution, [status(thm)], [c_38, c_2590])).
% 9.47/3.25  tff(c_3302, plain, (![E_814, B_815, A_816, F_813, C_812, D_817]: (k2_partfun1(k4_subset_1(A_816, C_812, D_817), B_815, k1_tmap_1(A_816, B_815, C_812, D_817, E_814, F_813), C_812)=E_814 | ~v1_funct_1(k1_tmap_1(A_816, B_815, C_812, D_817, E_814, F_813)) | k2_partfun1(D_817, B_815, F_813, k9_subset_1(A_816, C_812, D_817))!=k2_partfun1(C_812, B_815, E_814, k9_subset_1(A_816, C_812, D_817)) | ~m1_subset_1(F_813, k1_zfmisc_1(k2_zfmisc_1(D_817, B_815))) | ~v1_funct_2(F_813, D_817, B_815) | ~v1_funct_1(F_813) | ~m1_subset_1(E_814, k1_zfmisc_1(k2_zfmisc_1(C_812, B_815))) | ~v1_funct_2(E_814, C_812, B_815) | ~v1_funct_1(E_814) | ~m1_subset_1(D_817, k1_zfmisc_1(A_816)) | v1_xboole_0(D_817) | ~m1_subset_1(C_812, k1_zfmisc_1(A_816)) | v1_xboole_0(C_812) | v1_xboole_0(B_815) | v1_xboole_0(A_816))), inference(resolution, [status(thm)], [c_40, c_3237])).
% 9.47/3.25  tff(c_3306, plain, (![A_816, C_812, E_814]: (k2_partfun1(k4_subset_1(A_816, C_812, '#skF_6'), '#skF_4', k1_tmap_1(A_816, '#skF_4', C_812, '#skF_6', E_814, '#skF_8'), C_812)=E_814 | ~v1_funct_1(k1_tmap_1(A_816, '#skF_4', C_812, '#skF_6', E_814, '#skF_8')) | k2_partfun1(C_812, '#skF_4', E_814, k9_subset_1(A_816, C_812, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_816, C_812, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_814, k1_zfmisc_1(k2_zfmisc_1(C_812, '#skF_4'))) | ~v1_funct_2(E_814, C_812, '#skF_4') | ~v1_funct_1(E_814) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_816)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_812, k1_zfmisc_1(A_816)) | v1_xboole_0(C_812) | v1_xboole_0('#skF_4') | v1_xboole_0(A_816))), inference(resolution, [status(thm)], [c_46, c_3302])).
% 9.47/3.25  tff(c_3312, plain, (![A_816, C_812, E_814]: (k2_partfun1(k4_subset_1(A_816, C_812, '#skF_6'), '#skF_4', k1_tmap_1(A_816, '#skF_4', C_812, '#skF_6', E_814, '#skF_8'), C_812)=E_814 | ~v1_funct_1(k1_tmap_1(A_816, '#skF_4', C_812, '#skF_6', E_814, '#skF_8')) | k2_partfun1(C_812, '#skF_4', E_814, k9_subset_1(A_816, C_812, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_816, C_812, '#skF_6')) | ~m1_subset_1(E_814, k1_zfmisc_1(k2_zfmisc_1(C_812, '#skF_4'))) | ~v1_funct_2(E_814, C_812, '#skF_4') | ~v1_funct_1(E_814) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_816)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_812, k1_zfmisc_1(A_816)) | v1_xboole_0(C_812) | v1_xboole_0('#skF_4') | v1_xboole_0(A_816))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2199, c_3306])).
% 9.47/3.25  tff(c_3318, plain, (![A_818, C_819, E_820]: (k2_partfun1(k4_subset_1(A_818, C_819, '#skF_6'), '#skF_4', k1_tmap_1(A_818, '#skF_4', C_819, '#skF_6', E_820, '#skF_8'), C_819)=E_820 | ~v1_funct_1(k1_tmap_1(A_818, '#skF_4', C_819, '#skF_6', E_820, '#skF_8')) | k2_partfun1(C_819, '#skF_4', E_820, k9_subset_1(A_818, C_819, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_818, C_819, '#skF_6')) | ~m1_subset_1(E_820, k1_zfmisc_1(k2_zfmisc_1(C_819, '#skF_4'))) | ~v1_funct_2(E_820, C_819, '#skF_4') | ~v1_funct_1(E_820) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_818)) | ~m1_subset_1(C_819, k1_zfmisc_1(A_818)) | v1_xboole_0(C_819) | v1_xboole_0(A_818))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_3312])).
% 9.47/3.25  tff(c_3325, plain, (![A_818]: (k2_partfun1(k4_subset_1(A_818, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_818, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_818, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_818, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_818, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_818)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_818)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_818))), inference(resolution, [status(thm)], [c_52, c_3318])).
% 9.47/3.25  tff(c_3335, plain, (![A_818]: (k2_partfun1(k4_subset_1(A_818, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_818, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_818, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_818, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_818, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_818)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_818)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_818))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_2202, c_3325])).
% 9.47/3.25  tff(c_3380, plain, (![A_829]: (k2_partfun1(k4_subset_1(A_829, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_829, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_829, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_829, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_829, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_829)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_829)) | v1_xboole_0(A_829))), inference(negUnitSimplification, [status(thm)], [c_66, c_3335])).
% 9.47/3.25  tff(c_646, plain, (![A_332, B_333]: (k3_xboole_0(A_332, B_333)=k1_xboole_0 | ~r1_subset_1(A_332, B_333) | v1_xboole_0(B_333) | v1_xboole_0(A_332))), inference(resolution, [status(thm)], [c_499, c_6])).
% 9.47/3.25  tff(c_649, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_646])).
% 9.47/3.25  tff(c_652, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_62, c_649])).
% 9.47/3.25  tff(c_568, plain, (![A_321, B_322, C_323]: (k9_subset_1(A_321, B_322, C_323)=k3_xboole_0(B_322, C_323) | ~m1_subset_1(C_323, k1_zfmisc_1(A_321)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.47/3.25  tff(c_579, plain, (![B_322]: (k9_subset_1('#skF_3', B_322, '#skF_6')=k3_xboole_0(B_322, '#skF_6'))), inference(resolution, [status(thm)], [c_60, c_568])).
% 9.47/3.25  tff(c_795, plain, (![C_353, F_354, B_356, A_357, E_355, D_358]: (v1_funct_1(k1_tmap_1(A_357, B_356, C_353, D_358, E_355, F_354)) | ~m1_subset_1(F_354, k1_zfmisc_1(k2_zfmisc_1(D_358, B_356))) | ~v1_funct_2(F_354, D_358, B_356) | ~v1_funct_1(F_354) | ~m1_subset_1(E_355, k1_zfmisc_1(k2_zfmisc_1(C_353, B_356))) | ~v1_funct_2(E_355, C_353, B_356) | ~v1_funct_1(E_355) | ~m1_subset_1(D_358, k1_zfmisc_1(A_357)) | v1_xboole_0(D_358) | ~m1_subset_1(C_353, k1_zfmisc_1(A_357)) | v1_xboole_0(C_353) | v1_xboole_0(B_356) | v1_xboole_0(A_357))), inference(cnfTransformation, [status(thm)], [f_166])).
% 9.47/3.25  tff(c_797, plain, (![A_357, C_353, E_355]: (v1_funct_1(k1_tmap_1(A_357, '#skF_4', C_353, '#skF_6', E_355, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_355, k1_zfmisc_1(k2_zfmisc_1(C_353, '#skF_4'))) | ~v1_funct_2(E_355, C_353, '#skF_4') | ~v1_funct_1(E_355) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_357)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_353, k1_zfmisc_1(A_357)) | v1_xboole_0(C_353) | v1_xboole_0('#skF_4') | v1_xboole_0(A_357))), inference(resolution, [status(thm)], [c_46, c_795])).
% 9.47/3.25  tff(c_802, plain, (![A_357, C_353, E_355]: (v1_funct_1(k1_tmap_1(A_357, '#skF_4', C_353, '#skF_6', E_355, '#skF_8')) | ~m1_subset_1(E_355, k1_zfmisc_1(k2_zfmisc_1(C_353, '#skF_4'))) | ~v1_funct_2(E_355, C_353, '#skF_4') | ~v1_funct_1(E_355) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_357)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_353, k1_zfmisc_1(A_357)) | v1_xboole_0(C_353) | v1_xboole_0('#skF_4') | v1_xboole_0(A_357))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_797])).
% 9.47/3.25  tff(c_893, plain, (![A_379, C_380, E_381]: (v1_funct_1(k1_tmap_1(A_379, '#skF_4', C_380, '#skF_6', E_381, '#skF_8')) | ~m1_subset_1(E_381, k1_zfmisc_1(k2_zfmisc_1(C_380, '#skF_4'))) | ~v1_funct_2(E_381, C_380, '#skF_4') | ~v1_funct_1(E_381) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_379)) | ~m1_subset_1(C_380, k1_zfmisc_1(A_379)) | v1_xboole_0(C_380) | v1_xboole_0(A_379))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_802])).
% 9.47/3.25  tff(c_897, plain, (![A_379]: (v1_funct_1(k1_tmap_1(A_379, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_379)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_379)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_379))), inference(resolution, [status(thm)], [c_52, c_893])).
% 9.47/3.25  tff(c_904, plain, (![A_379]: (v1_funct_1(k1_tmap_1(A_379, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_379)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_379)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_379))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_897])).
% 9.47/3.25  tff(c_1091, plain, (![A_427]: (v1_funct_1(k1_tmap_1(A_427, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_427)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_427)) | v1_xboole_0(A_427))), inference(negUnitSimplification, [status(thm)], [c_66, c_904])).
% 9.47/3.25  tff(c_1094, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1091])).
% 9.47/3.25  tff(c_1097, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1094])).
% 9.47/3.25  tff(c_1098, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1097])).
% 9.47/3.25  tff(c_752, plain, (![A_347, B_348, C_349, D_350]: (k2_partfun1(A_347, B_348, C_349, D_350)=k7_relat_1(C_349, D_350) | ~m1_subset_1(C_349, k1_zfmisc_1(k2_zfmisc_1(A_347, B_348))) | ~v1_funct_1(C_349))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.47/3.25  tff(c_756, plain, (![D_350]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_350)=k7_relat_1('#skF_7', D_350) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_52, c_752])).
% 9.47/3.25  tff(c_762, plain, (![D_350]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_350)=k7_relat_1('#skF_7', D_350))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_756])).
% 9.47/3.25  tff(c_754, plain, (![D_350]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_350)=k7_relat_1('#skF_8', D_350) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_46, c_752])).
% 9.47/3.25  tff(c_759, plain, (![D_350]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_350)=k7_relat_1('#skF_8', D_350))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_754])).
% 9.47/3.25  tff(c_1135, plain, (![C_439, D_436, F_438, E_440, B_437, A_435]: (k2_partfun1(k4_subset_1(A_435, C_439, D_436), B_437, k1_tmap_1(A_435, B_437, C_439, D_436, E_440, F_438), D_436)=F_438 | ~m1_subset_1(k1_tmap_1(A_435, B_437, C_439, D_436, E_440, F_438), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_435, C_439, D_436), B_437))) | ~v1_funct_2(k1_tmap_1(A_435, B_437, C_439, D_436, E_440, F_438), k4_subset_1(A_435, C_439, D_436), B_437) | ~v1_funct_1(k1_tmap_1(A_435, B_437, C_439, D_436, E_440, F_438)) | k2_partfun1(D_436, B_437, F_438, k9_subset_1(A_435, C_439, D_436))!=k2_partfun1(C_439, B_437, E_440, k9_subset_1(A_435, C_439, D_436)) | ~m1_subset_1(F_438, k1_zfmisc_1(k2_zfmisc_1(D_436, B_437))) | ~v1_funct_2(F_438, D_436, B_437) | ~v1_funct_1(F_438) | ~m1_subset_1(E_440, k1_zfmisc_1(k2_zfmisc_1(C_439, B_437))) | ~v1_funct_2(E_440, C_439, B_437) | ~v1_funct_1(E_440) | ~m1_subset_1(D_436, k1_zfmisc_1(A_435)) | v1_xboole_0(D_436) | ~m1_subset_1(C_439, k1_zfmisc_1(A_435)) | v1_xboole_0(C_439) | v1_xboole_0(B_437) | v1_xboole_0(A_435))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.47/3.25  tff(c_1790, plain, (![A_540, C_536, F_537, E_538, D_541, B_539]: (k2_partfun1(k4_subset_1(A_540, C_536, D_541), B_539, k1_tmap_1(A_540, B_539, C_536, D_541, E_538, F_537), D_541)=F_537 | ~v1_funct_2(k1_tmap_1(A_540, B_539, C_536, D_541, E_538, F_537), k4_subset_1(A_540, C_536, D_541), B_539) | ~v1_funct_1(k1_tmap_1(A_540, B_539, C_536, D_541, E_538, F_537)) | k2_partfun1(D_541, B_539, F_537, k9_subset_1(A_540, C_536, D_541))!=k2_partfun1(C_536, B_539, E_538, k9_subset_1(A_540, C_536, D_541)) | ~m1_subset_1(F_537, k1_zfmisc_1(k2_zfmisc_1(D_541, B_539))) | ~v1_funct_2(F_537, D_541, B_539) | ~v1_funct_1(F_537) | ~m1_subset_1(E_538, k1_zfmisc_1(k2_zfmisc_1(C_536, B_539))) | ~v1_funct_2(E_538, C_536, B_539) | ~v1_funct_1(E_538) | ~m1_subset_1(D_541, k1_zfmisc_1(A_540)) | v1_xboole_0(D_541) | ~m1_subset_1(C_536, k1_zfmisc_1(A_540)) | v1_xboole_0(C_536) | v1_xboole_0(B_539) | v1_xboole_0(A_540))), inference(resolution, [status(thm)], [c_38, c_1135])).
% 9.47/3.25  tff(c_1844, plain, (![D_555, C_550, E_552, B_553, F_551, A_554]: (k2_partfun1(k4_subset_1(A_554, C_550, D_555), B_553, k1_tmap_1(A_554, B_553, C_550, D_555, E_552, F_551), D_555)=F_551 | ~v1_funct_1(k1_tmap_1(A_554, B_553, C_550, D_555, E_552, F_551)) | k2_partfun1(D_555, B_553, F_551, k9_subset_1(A_554, C_550, D_555))!=k2_partfun1(C_550, B_553, E_552, k9_subset_1(A_554, C_550, D_555)) | ~m1_subset_1(F_551, k1_zfmisc_1(k2_zfmisc_1(D_555, B_553))) | ~v1_funct_2(F_551, D_555, B_553) | ~v1_funct_1(F_551) | ~m1_subset_1(E_552, k1_zfmisc_1(k2_zfmisc_1(C_550, B_553))) | ~v1_funct_2(E_552, C_550, B_553) | ~v1_funct_1(E_552) | ~m1_subset_1(D_555, k1_zfmisc_1(A_554)) | v1_xboole_0(D_555) | ~m1_subset_1(C_550, k1_zfmisc_1(A_554)) | v1_xboole_0(C_550) | v1_xboole_0(B_553) | v1_xboole_0(A_554))), inference(resolution, [status(thm)], [c_40, c_1790])).
% 9.47/3.25  tff(c_1848, plain, (![A_554, C_550, E_552]: (k2_partfun1(k4_subset_1(A_554, C_550, '#skF_6'), '#skF_4', k1_tmap_1(A_554, '#skF_4', C_550, '#skF_6', E_552, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_554, '#skF_4', C_550, '#skF_6', E_552, '#skF_8')) | k2_partfun1(C_550, '#skF_4', E_552, k9_subset_1(A_554, C_550, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_554, C_550, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_552, k1_zfmisc_1(k2_zfmisc_1(C_550, '#skF_4'))) | ~v1_funct_2(E_552, C_550, '#skF_4') | ~v1_funct_1(E_552) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_554)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_550, k1_zfmisc_1(A_554)) | v1_xboole_0(C_550) | v1_xboole_0('#skF_4') | v1_xboole_0(A_554))), inference(resolution, [status(thm)], [c_46, c_1844])).
% 9.47/3.25  tff(c_1854, plain, (![A_554, C_550, E_552]: (k2_partfun1(k4_subset_1(A_554, C_550, '#skF_6'), '#skF_4', k1_tmap_1(A_554, '#skF_4', C_550, '#skF_6', E_552, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_554, '#skF_4', C_550, '#skF_6', E_552, '#skF_8')) | k2_partfun1(C_550, '#skF_4', E_552, k9_subset_1(A_554, C_550, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_554, C_550, '#skF_6')) | ~m1_subset_1(E_552, k1_zfmisc_1(k2_zfmisc_1(C_550, '#skF_4'))) | ~v1_funct_2(E_552, C_550, '#skF_4') | ~v1_funct_1(E_552) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_554)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_550, k1_zfmisc_1(A_554)) | v1_xboole_0(C_550) | v1_xboole_0('#skF_4') | v1_xboole_0(A_554))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_759, c_1848])).
% 9.47/3.25  tff(c_1860, plain, (![A_556, C_557, E_558]: (k2_partfun1(k4_subset_1(A_556, C_557, '#skF_6'), '#skF_4', k1_tmap_1(A_556, '#skF_4', C_557, '#skF_6', E_558, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_556, '#skF_4', C_557, '#skF_6', E_558, '#skF_8')) | k2_partfun1(C_557, '#skF_4', E_558, k9_subset_1(A_556, C_557, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_556, C_557, '#skF_6')) | ~m1_subset_1(E_558, k1_zfmisc_1(k2_zfmisc_1(C_557, '#skF_4'))) | ~v1_funct_2(E_558, C_557, '#skF_4') | ~v1_funct_1(E_558) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_556)) | ~m1_subset_1(C_557, k1_zfmisc_1(A_556)) | v1_xboole_0(C_557) | v1_xboole_0(A_556))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_1854])).
% 9.47/3.25  tff(c_1867, plain, (![A_556]: (k2_partfun1(k4_subset_1(A_556, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_556, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_556, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_556, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_556, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_556)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_556)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_556))), inference(resolution, [status(thm)], [c_52, c_1860])).
% 9.47/3.25  tff(c_1877, plain, (![A_556]: (k2_partfun1(k4_subset_1(A_556, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_556, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_556, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_556, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_556, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_556)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_556)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_556))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_762, c_1867])).
% 9.47/3.25  tff(c_1922, plain, (![A_567]: (k2_partfun1(k4_subset_1(A_567, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_567, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_567, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_567, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_567, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_567)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_567)) | v1_xboole_0(A_567))), inference(negUnitSimplification, [status(thm)], [c_66, c_1877])).
% 9.47/3.25  tff(c_93, plain, (![A_226, B_227]: (r2_hidden('#skF_2'(A_226, B_227), B_227) | r1_xboole_0(A_226, B_227))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.47/3.25  tff(c_97, plain, (![B_227, A_226]: (~v1_xboole_0(B_227) | r1_xboole_0(A_226, B_227))), inference(resolution, [status(thm)], [c_93, c_2])).
% 9.47/3.25  tff(c_161, plain, (![B_245, A_246]: (k7_relat_1(B_245, A_246)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_245), A_246) | ~v1_relat_1(B_245))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.47/3.25  tff(c_182, plain, (![B_247, B_248]: (k7_relat_1(B_247, B_248)=k1_xboole_0 | ~v1_relat_1(B_247) | ~v1_xboole_0(B_248))), inference(resolution, [status(thm)], [c_97, c_161])).
% 9.47/3.25  tff(c_201, plain, (![B_251]: (k7_relat_1('#skF_7', B_251)=k1_xboole_0 | ~v1_xboole_0(B_251))), inference(resolution, [status(thm)], [c_91, c_182])).
% 9.47/3.25  tff(c_205, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_201])).
% 9.47/3.25  tff(c_357, plain, (![A_277, B_278, C_279, D_280]: (k2_partfun1(A_277, B_278, C_279, D_280)=k7_relat_1(C_279, D_280) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_277, B_278))) | ~v1_funct_1(C_279))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.47/3.25  tff(c_361, plain, (![D_280]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_280)=k7_relat_1('#skF_7', D_280) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_52, c_357])).
% 9.47/3.25  tff(c_367, plain, (![D_280]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_280)=k7_relat_1('#skF_7', D_280))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_361])).
% 9.47/3.25  tff(c_210, plain, (![B_252]: (k7_relat_1('#skF_8', B_252)=k1_xboole_0 | ~v1_xboole_0(B_252))), inference(resolution, [status(thm)], [c_90, c_182])).
% 9.47/3.25  tff(c_214, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_210])).
% 9.47/3.25  tff(c_359, plain, (![D_280]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_280)=k7_relat_1('#skF_8', D_280) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_46, c_357])).
% 9.47/3.25  tff(c_364, plain, (![D_280]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_280)=k7_relat_1('#skF_8', D_280))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_359])).
% 9.47/3.25  tff(c_153, plain, (![A_243, B_244]: (r1_xboole_0(A_243, B_244) | ~r1_subset_1(A_243, B_244) | v1_xboole_0(B_244) | v1_xboole_0(A_243))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.47/3.25  tff(c_317, plain, (![A_270, B_271]: (k3_xboole_0(A_270, B_271)=k1_xboole_0 | ~r1_subset_1(A_270, B_271) | v1_xboole_0(B_271) | v1_xboole_0(A_270))), inference(resolution, [status(thm)], [c_153, c_6])).
% 9.47/3.25  tff(c_320, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_317])).
% 9.47/3.25  tff(c_323, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_62, c_320])).
% 9.47/3.25  tff(c_267, plain, (![A_263, B_264, C_265]: (k9_subset_1(A_263, B_264, C_265)=k3_xboole_0(B_264, C_265) | ~m1_subset_1(C_265, k1_zfmisc_1(A_263)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.47/3.25  tff(c_278, plain, (![B_264]: (k9_subset_1('#skF_3', B_264, '#skF_6')=k3_xboole_0(B_264, '#skF_6'))), inference(resolution, [status(thm)], [c_60, c_267])).
% 9.47/3.25  tff(c_44, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.25  tff(c_92, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_44])).
% 9.47/3.25  tff(c_280, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k3_xboole_0('#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_278, c_278, c_92])).
% 9.47/3.25  tff(c_397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_367, c_214, c_364, c_323, c_323, c_280])).
% 9.47/3.25  tff(c_398, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_44])).
% 9.47/3.25  tff(c_526, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitLeft, [status(thm)], [c_398])).
% 9.47/3.25  tff(c_1933, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1922, c_526])).
% 9.47/3.25  tff(c_1947, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_525, c_652, c_516, c_652, c_579, c_579, c_1098, c_1933])).
% 9.47/3.25  tff(c_1949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1947])).
% 9.47/3.25  tff(c_1950, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_398])).
% 9.47/3.25  tff(c_3389, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3380, c_1950])).
% 9.47/3.25  tff(c_3400, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_525, c_2060, c_516, c_2060, c_2015, c_2015, c_2740, c_3389])).
% 9.47/3.25  tff(c_3402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_3400])).
% 9.47/3.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.47/3.25  
% 9.47/3.25  Inference rules
% 9.47/3.25  ----------------------
% 9.47/3.25  #Ref     : 0
% 9.47/3.25  #Sup     : 718
% 9.47/3.25  #Fact    : 0
% 9.47/3.25  #Define  : 0
% 9.47/3.25  #Split   : 2
% 9.47/3.25  #Chain   : 0
% 9.47/3.25  #Close   : 0
% 9.47/3.25  
% 9.47/3.25  Ordering : KBO
% 9.47/3.25  
% 9.47/3.25  Simplification rules
% 9.47/3.25  ----------------------
% 9.47/3.25  #Subsume      : 152
% 9.47/3.25  #Demod        : 282
% 9.47/3.25  #Tautology    : 270
% 9.47/3.25  #SimpNegUnit  : 107
% 9.47/3.25  #BackRed      : 5
% 9.47/3.25  
% 9.47/3.25  #Partial instantiations: 0
% 9.47/3.25  #Strategies tried      : 1
% 9.47/3.25  
% 9.47/3.25  Timing (in seconds)
% 9.47/3.25  ----------------------
% 9.47/3.25  Preprocessing        : 0.64
% 9.47/3.25  Parsing              : 0.29
% 9.47/3.26  CNF conversion       : 0.10
% 9.47/3.26  Main loop            : 1.79
% 9.47/3.26  Inferencing          : 0.69
% 9.47/3.26  Reduction            : 0.54
% 9.47/3.26  Demodulation         : 0.37
% 9.47/3.26  BG Simplification    : 0.07
% 9.47/3.26  Subsumption          : 0.37
% 9.47/3.26  Abstraction          : 0.08
% 9.47/3.26  MUC search           : 0.00
% 9.47/3.26  Cooper               : 0.00
% 9.47/3.26  Total                : 2.49
% 9.47/3.26  Index Insertion      : 0.00
% 9.47/3.26  Index Deletion       : 0.00
% 9.47/3.26  Index Matching       : 0.00
% 9.47/3.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
