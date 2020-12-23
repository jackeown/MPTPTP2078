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
% DateTime   : Thu Dec  3 10:26:08 EST 2020

% Result     : Theorem 12.36s
% Output     : CNFRefutation 12.49s
% Verified   : 
% Statistics : Number of formulae       :  226 ( 787 expanded)
%              Number of leaves         :   52 ( 304 expanded)
%              Depth                    :   12
%              Number of atoms          :  754 (3853 expanded)
%              Number of equality atoms :  150 ( 767 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_268,negated_conjecture,(
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

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_funct_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( ( k1_relat_1(B) = k3_xboole_0(k1_relat_1(C),A)
              & ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                 => k1_funct_1(B,D) = k1_funct_1(C,D) ) )
           => B = k7_relat_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_funct_1)).

tff(f_88,axiom,(
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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_144,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_138,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_226,axiom,(
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

tff(f_192,axiom,(
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

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_84,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_80,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_70,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_66,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_1486,plain,(
    ! [C_460,A_461,B_462] :
      ( v1_relat_1(C_460)
      | ~ m1_subset_1(C_460,k1_zfmisc_1(k2_zfmisc_1(A_461,B_462))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1498,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_1486])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_7181,plain,(
    ! [A_1574,B_1575,C_1576] :
      ( ~ r1_xboole_0(A_1574,B_1575)
      | ~ r2_hidden(C_1576,k3_xboole_0(A_1574,B_1575)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7184,plain,(
    ! [A_8,C_1576] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_1576,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_7181])).

tff(c_7186,plain,(
    ! [C_1576] : ~ r2_hidden(C_1576,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_7184])).

tff(c_16,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1499,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_1486])).

tff(c_7246,plain,(
    ! [B_1589,A_1590] :
      ( v1_funct_1(B_1589)
      | ~ m1_subset_1(B_1589,k1_zfmisc_1(A_1590))
      | ~ v1_funct_1(A_1590)
      | ~ v1_relat_1(A_1590) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7267,plain,(
    ! [A_13] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_16,c_7246])).

tff(c_7287,plain,(
    ! [A_1594] :
      ( ~ v1_funct_1(A_1594)
      | ~ v1_relat_1(A_1594) ) ),
    inference(splitLeft,[status(thm)],[c_7267])).

tff(c_7293,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1498,c_7287])).

tff(c_7301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_7293])).

tff(c_7302,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7267])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_11084,plain,(
    ! [A_2226,B_2227,C_2228] :
      ( r2_hidden('#skF_2'(A_2226,B_2227,C_2228),k1_relat_1(B_2227))
      | k7_relat_1(C_2228,A_2226) = B_2227
      | k3_xboole_0(k1_relat_1(C_2228),A_2226) != k1_relat_1(B_2227)
      | ~ v1_funct_1(C_2228)
      | ~ v1_relat_1(C_2228)
      | ~ v1_funct_1(B_2227)
      | ~ v1_relat_1(B_2227) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_11093,plain,(
    ! [A_2226,C_2228] :
      ( r2_hidden('#skF_2'(A_2226,k1_xboole_0,C_2228),k1_xboole_0)
      | k7_relat_1(C_2228,A_2226) = k1_xboole_0
      | k3_xboole_0(k1_relat_1(C_2228),A_2226) != k1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(C_2228)
      | ~ v1_relat_1(C_2228)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_11084])).

tff(c_11099,plain,(
    ! [A_2226,C_2228] :
      ( r2_hidden('#skF_2'(A_2226,k1_xboole_0,C_2228),k1_xboole_0)
      | k7_relat_1(C_2228,A_2226) = k1_xboole_0
      | k3_xboole_0(k1_relat_1(C_2228),A_2226) != k1_xboole_0
      | ~ v1_funct_1(C_2228)
      | ~ v1_relat_1(C_2228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1499,c_7302,c_24,c_11093])).

tff(c_11101,plain,(
    ! [C_2229,A_2230] :
      ( k7_relat_1(C_2229,A_2230) = k1_xboole_0
      | k3_xboole_0(k1_relat_1(C_2229),A_2230) != k1_xboole_0
      | ~ v1_funct_1(C_2229)
      | ~ v1_relat_1(C_2229) ) ),
    inference(negUnitSimplification,[status(thm)],[c_7186,c_11099])).

tff(c_11122,plain,(
    ! [C_2231] :
      ( k7_relat_1(C_2231,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_2231)
      | ~ v1_relat_1(C_2231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_11101])).

tff(c_11128,plain,
    ( k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1498,c_11122])).

tff(c_11137,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_11128])).

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_78,plain,(
    r1_subset_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_10526,plain,(
    ! [A_2149,B_2150] :
      ( r1_xboole_0(A_2149,B_2150)
      | ~ r1_subset_1(A_2149,B_2150)
      | v1_xboole_0(B_2150)
      | v1_xboole_0(A_2149) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_11023,plain,(
    ! [A_2219,B_2220] :
      ( k3_xboole_0(A_2219,B_2220) = k1_xboole_0
      | ~ r1_subset_1(A_2219,B_2220)
      | v1_xboole_0(B_2220)
      | v1_xboole_0(A_2219) ) ),
    inference(resolution,[status(thm)],[c_10526,c_2])).

tff(c_11029,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_11023])).

tff(c_11033,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_82,c_11029])).

tff(c_10535,plain,(
    ! [A_2151,B_2152,C_2153] :
      ( k9_subset_1(A_2151,B_2152,C_2153) = k3_xboole_0(B_2152,C_2153)
      | ~ m1_subset_1(C_2153,k1_zfmisc_1(A_2151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10548,plain,(
    ! [B_2152] : k9_subset_1('#skF_3',B_2152,'#skF_6') = k3_xboole_0(B_2152,'#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_10535])).

tff(c_10978,plain,(
    ! [A_2210,B_2211,C_2212,D_2213] :
      ( k2_partfun1(A_2210,B_2211,C_2212,D_2213) = k7_relat_1(C_2212,D_2213)
      | ~ m1_subset_1(C_2212,k1_zfmisc_1(k2_zfmisc_1(A_2210,B_2211)))
      | ~ v1_funct_1(C_2212) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_10982,plain,(
    ! [D_2213] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_2213) = k7_relat_1('#skF_8',D_2213)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_66,c_10978])).

tff(c_10991,plain,(
    ! [D_2213] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_2213) = k7_relat_1('#skF_8',D_2213) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_10982])).

tff(c_76,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_72,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_10980,plain,(
    ! [D_2213] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_2213) = k7_relat_1('#skF_7',D_2213)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_10978])).

tff(c_10988,plain,(
    ! [D_2213] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_2213) = k7_relat_1('#skF_7',D_2213) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_10980])).

tff(c_120,plain,(
    ! [C_245,A_246,B_247] :
      ( v1_relat_1(C_245)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_131,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_120])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_776,plain,(
    ! [C_352,A_353,B_354] :
      ( v4_relat_1(C_352,A_353)
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_787,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_776])).

tff(c_895,plain,(
    ! [B_373,A_374] :
      ( k1_relat_1(B_373) = A_374
      | ~ v1_partfun1(B_373,A_374)
      | ~ v4_relat_1(B_373,A_374)
      | ~ v1_relat_1(B_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_904,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_787,c_895])).

tff(c_913,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_904])).

tff(c_914,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_913])).

tff(c_74,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_1034,plain,(
    ! [C_396,A_397,B_398] :
      ( v1_partfun1(C_396,A_397)
      | ~ v1_funct_2(C_396,A_397,B_398)
      | ~ v1_funct_1(C_396)
      | ~ m1_subset_1(C_396,k1_zfmisc_1(k2_zfmisc_1(A_397,B_398)))
      | v1_xboole_0(B_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1037,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1034])).

tff(c_1047,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1037])).

tff(c_1049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_914,c_1047])).

tff(c_1050,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_913])).

tff(c_753,plain,(
    ! [A_344,B_345,C_346] :
      ( ~ r1_xboole_0(A_344,B_345)
      | ~ r2_hidden(C_346,k3_xboole_0(A_344,B_345)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_756,plain,(
    ! [A_8,C_346] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_346,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_753])).

tff(c_758,plain,(
    ! [C_346] : ~ r2_hidden(C_346,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_756])).

tff(c_133,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_120])).

tff(c_132,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_120])).

tff(c_825,plain,(
    ! [B_366,A_367] :
      ( v1_funct_1(B_366)
      | ~ m1_subset_1(B_366,k1_zfmisc_1(A_367))
      | ~ v1_funct_1(A_367)
      | ~ v1_relat_1(A_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_846,plain,(
    ! [A_13] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_16,c_825])).

tff(c_850,plain,(
    ! [A_368] :
      ( ~ v1_funct_1(A_368)
      | ~ v1_relat_1(A_368) ) ),
    inference(splitLeft,[status(thm)],[c_846])).

tff(c_856,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_132,c_850])).

tff(c_864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_856])).

tff(c_865,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_846])).

tff(c_1404,plain,(
    ! [A_451,B_452,C_453] :
      ( r2_hidden('#skF_2'(A_451,B_452,C_453),k1_relat_1(B_452))
      | k7_relat_1(C_453,A_451) = B_452
      | k3_xboole_0(k1_relat_1(C_453),A_451) != k1_relat_1(B_452)
      | ~ v1_funct_1(C_453)
      | ~ v1_relat_1(C_453)
      | ~ v1_funct_1(B_452)
      | ~ v1_relat_1(B_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1413,plain,(
    ! [A_451,C_453] :
      ( r2_hidden('#skF_2'(A_451,k1_xboole_0,C_453),k1_xboole_0)
      | k7_relat_1(C_453,A_451) = k1_xboole_0
      | k3_xboole_0(k1_relat_1(C_453),A_451) != k1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(C_453)
      | ~ v1_relat_1(C_453)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1404])).

tff(c_1419,plain,(
    ! [A_451,C_453] :
      ( r2_hidden('#skF_2'(A_451,k1_xboole_0,C_453),k1_xboole_0)
      | k7_relat_1(C_453,A_451) = k1_xboole_0
      | k3_xboole_0(k1_relat_1(C_453),A_451) != k1_xboole_0
      | ~ v1_funct_1(C_453)
      | ~ v1_relat_1(C_453) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_865,c_24,c_1413])).

tff(c_1421,plain,(
    ! [C_454,A_455] :
      ( k7_relat_1(C_454,A_455) = k1_xboole_0
      | k3_xboole_0(k1_relat_1(C_454),A_455) != k1_xboole_0
      | ~ v1_funct_1(C_454)
      | ~ v1_relat_1(C_454) ) ),
    inference(negUnitSimplification,[status(thm)],[c_758,c_1419])).

tff(c_1427,plain,(
    ! [A_455] :
      ( k7_relat_1('#skF_7',A_455) = k1_xboole_0
      | k3_xboole_0('#skF_5',A_455) != k1_xboole_0
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1050,c_1421])).

tff(c_1442,plain,(
    ! [A_456] :
      ( k7_relat_1('#skF_7',A_456) = k1_xboole_0
      | k3_xboole_0('#skF_5',A_456) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_76,c_1427])).

tff(c_791,plain,(
    ! [A_356,B_357] :
      ( r1_xboole_0(A_356,B_357)
      | ~ r1_subset_1(A_356,B_357)
      | v1_xboole_0(B_357)
      | v1_xboole_0(A_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1346,plain,(
    ! [A_442,B_443] :
      ( k3_xboole_0(A_442,B_443) = k1_xboole_0
      | ~ r1_subset_1(A_442,B_443)
      | v1_xboole_0(B_443)
      | v1_xboole_0(A_442) ) ),
    inference(resolution,[status(thm)],[c_791,c_2])).

tff(c_1349,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_1346])).

tff(c_1352,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_82,c_1349])).

tff(c_1293,plain,(
    ! [A_432,B_433,C_434,D_435] :
      ( k2_partfun1(A_432,B_433,C_434,D_435) = k7_relat_1(C_434,D_435)
      | ~ m1_subset_1(C_434,k1_zfmisc_1(k2_zfmisc_1(A_432,B_433)))
      | ~ v1_funct_1(C_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1297,plain,(
    ! [D_435] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_435) = k7_relat_1('#skF_8',D_435)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_66,c_1293])).

tff(c_1306,plain,(
    ! [D_435] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_435) = k7_relat_1('#skF_8',D_435) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1297])).

tff(c_1295,plain,(
    ! [D_435] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_435) = k7_relat_1('#skF_7',D_435)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_1293])).

tff(c_1303,plain,(
    ! [D_435] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_435) = k7_relat_1('#skF_7',D_435) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1295])).

tff(c_1235,plain,(
    ! [A_423,B_424,C_425] :
      ( k9_subset_1(A_423,B_424,C_425) = k3_xboole_0(B_424,C_425)
      | ~ m1_subset_1(C_425,k1_zfmisc_1(A_423)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1248,plain,(
    ! [B_424] : k9_subset_1('#skF_3',B_424,'#skF_6') = k3_xboole_0(B_424,'#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_1235])).

tff(c_64,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_109,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_1265,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k3_xboole_0('#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_1248,c_109])).

tff(c_1380,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) != k7_relat_1('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1352,c_1352,c_1306,c_1303,c_1265])).

tff(c_1448,plain,
    ( k7_relat_1('#skF_8',k1_xboole_0) != k1_xboole_0
    | k3_xboole_0('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1442,c_1380])).

tff(c_1454,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1448])).

tff(c_1456,plain,(
    ! [C_457] :
      ( k7_relat_1(C_457,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_457)
      | ~ v1_relat_1(C_457) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1421])).

tff(c_1462,plain,
    ( k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_132,c_1456])).

tff(c_1471,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1462])).

tff(c_1473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1454,c_1471])).

tff(c_1475,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) = k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_10559,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k3_xboole_0('#skF_5','#skF_6')) = k2_partfun1('#skF_6','#skF_4','#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10548,c_10548,c_1475])).

tff(c_10995,plain,(
    k2_partfun1('#skF_6','#skF_4','#skF_8',k3_xboole_0('#skF_5','#skF_6')) = k7_relat_1('#skF_7',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10988,c_10559])).

tff(c_11079,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k7_relat_1('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11033,c_11033,c_10991,c_10995])).

tff(c_11145,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11137,c_11079])).

tff(c_68,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_11266,plain,(
    ! [E_2245,D_2242,A_2243,F_2244,C_2241,B_2246] :
      ( v1_funct_1(k1_tmap_1(A_2243,B_2246,C_2241,D_2242,E_2245,F_2244))
      | ~ m1_subset_1(F_2244,k1_zfmisc_1(k2_zfmisc_1(D_2242,B_2246)))
      | ~ v1_funct_2(F_2244,D_2242,B_2246)
      | ~ v1_funct_1(F_2244)
      | ~ m1_subset_1(E_2245,k1_zfmisc_1(k2_zfmisc_1(C_2241,B_2246)))
      | ~ v1_funct_2(E_2245,C_2241,B_2246)
      | ~ v1_funct_1(E_2245)
      | ~ m1_subset_1(D_2242,k1_zfmisc_1(A_2243))
      | v1_xboole_0(D_2242)
      | ~ m1_subset_1(C_2241,k1_zfmisc_1(A_2243))
      | v1_xboole_0(C_2241)
      | v1_xboole_0(B_2246)
      | v1_xboole_0(A_2243) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_11270,plain,(
    ! [A_2243,C_2241,E_2245] :
      ( v1_funct_1(k1_tmap_1(A_2243,'#skF_4',C_2241,'#skF_6',E_2245,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_2245,k1_zfmisc_1(k2_zfmisc_1(C_2241,'#skF_4')))
      | ~ v1_funct_2(E_2245,C_2241,'#skF_4')
      | ~ v1_funct_1(E_2245)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2243))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_2241,k1_zfmisc_1(A_2243))
      | v1_xboole_0(C_2241)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2243) ) ),
    inference(resolution,[status(thm)],[c_66,c_11266])).

tff(c_11280,plain,(
    ! [A_2243,C_2241,E_2245] :
      ( v1_funct_1(k1_tmap_1(A_2243,'#skF_4',C_2241,'#skF_6',E_2245,'#skF_8'))
      | ~ m1_subset_1(E_2245,k1_zfmisc_1(k2_zfmisc_1(C_2241,'#skF_4')))
      | ~ v1_funct_2(E_2245,C_2241,'#skF_4')
      | ~ v1_funct_1(E_2245)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2243))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_2241,k1_zfmisc_1(A_2243))
      | v1_xboole_0(C_2241)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_11270])).

tff(c_11309,plain,(
    ! [A_2248,C_2249,E_2250] :
      ( v1_funct_1(k1_tmap_1(A_2248,'#skF_4',C_2249,'#skF_6',E_2250,'#skF_8'))
      | ~ m1_subset_1(E_2250,k1_zfmisc_1(k2_zfmisc_1(C_2249,'#skF_4')))
      | ~ v1_funct_2(E_2250,C_2249,'#skF_4')
      | ~ v1_funct_1(E_2250)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2248))
      | ~ m1_subset_1(C_2249,k1_zfmisc_1(A_2248))
      | v1_xboole_0(C_2249)
      | v1_xboole_0(A_2248) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_11280])).

tff(c_11311,plain,(
    ! [A_2248] :
      ( v1_funct_1(k1_tmap_1(A_2248,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2248))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2248))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_2248) ) ),
    inference(resolution,[status(thm)],[c_72,c_11309])).

tff(c_11319,plain,(
    ! [A_2248] :
      ( v1_funct_1(k1_tmap_1(A_2248,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2248))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2248))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_2248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_11311])).

tff(c_11373,plain,(
    ! [A_2261] :
      ( v1_funct_1(k1_tmap_1(A_2261,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2261))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2261))
      | v1_xboole_0(A_2261) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_11319])).

tff(c_11376,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_11373])).

tff(c_11379,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_11376])).

tff(c_11380,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_11379])).

tff(c_60,plain,(
    ! [C_177,F_180,A_175,D_178,B_176,E_179] :
      ( v1_funct_2(k1_tmap_1(A_175,B_176,C_177,D_178,E_179,F_180),k4_subset_1(A_175,C_177,D_178),B_176)
      | ~ m1_subset_1(F_180,k1_zfmisc_1(k2_zfmisc_1(D_178,B_176)))
      | ~ v1_funct_2(F_180,D_178,B_176)
      | ~ v1_funct_1(F_180)
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(C_177,B_176)))
      | ~ v1_funct_2(E_179,C_177,B_176)
      | ~ v1_funct_1(E_179)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(A_175))
      | v1_xboole_0(D_178)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(A_175))
      | v1_xboole_0(C_177)
      | v1_xboole_0(B_176)
      | v1_xboole_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_58,plain,(
    ! [C_177,F_180,A_175,D_178,B_176,E_179] :
      ( m1_subset_1(k1_tmap_1(A_175,B_176,C_177,D_178,E_179,F_180),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_175,C_177,D_178),B_176)))
      | ~ m1_subset_1(F_180,k1_zfmisc_1(k2_zfmisc_1(D_178,B_176)))
      | ~ v1_funct_2(F_180,D_178,B_176)
      | ~ v1_funct_1(F_180)
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(C_177,B_176)))
      | ~ v1_funct_2(E_179,C_177,B_176)
      | ~ v1_funct_1(E_179)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(A_175))
      | v1_xboole_0(D_178)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(A_175))
      | v1_xboole_0(C_177)
      | v1_xboole_0(B_176)
      | v1_xboole_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_11488,plain,(
    ! [D_2285,E_2282,B_2287,A_2283,C_2284,F_2286] :
      ( k2_partfun1(k4_subset_1(A_2283,C_2284,D_2285),B_2287,k1_tmap_1(A_2283,B_2287,C_2284,D_2285,E_2282,F_2286),C_2284) = E_2282
      | ~ m1_subset_1(k1_tmap_1(A_2283,B_2287,C_2284,D_2285,E_2282,F_2286),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2283,C_2284,D_2285),B_2287)))
      | ~ v1_funct_2(k1_tmap_1(A_2283,B_2287,C_2284,D_2285,E_2282,F_2286),k4_subset_1(A_2283,C_2284,D_2285),B_2287)
      | ~ v1_funct_1(k1_tmap_1(A_2283,B_2287,C_2284,D_2285,E_2282,F_2286))
      | k2_partfun1(D_2285,B_2287,F_2286,k9_subset_1(A_2283,C_2284,D_2285)) != k2_partfun1(C_2284,B_2287,E_2282,k9_subset_1(A_2283,C_2284,D_2285))
      | ~ m1_subset_1(F_2286,k1_zfmisc_1(k2_zfmisc_1(D_2285,B_2287)))
      | ~ v1_funct_2(F_2286,D_2285,B_2287)
      | ~ v1_funct_1(F_2286)
      | ~ m1_subset_1(E_2282,k1_zfmisc_1(k2_zfmisc_1(C_2284,B_2287)))
      | ~ v1_funct_2(E_2282,C_2284,B_2287)
      | ~ v1_funct_1(E_2282)
      | ~ m1_subset_1(D_2285,k1_zfmisc_1(A_2283))
      | v1_xboole_0(D_2285)
      | ~ m1_subset_1(C_2284,k1_zfmisc_1(A_2283))
      | v1_xboole_0(C_2284)
      | v1_xboole_0(B_2287)
      | v1_xboole_0(A_2283) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_12457,plain,(
    ! [A_2479,D_2478,B_2482,E_2481,F_2480,C_2477] :
      ( k2_partfun1(k4_subset_1(A_2479,C_2477,D_2478),B_2482,k1_tmap_1(A_2479,B_2482,C_2477,D_2478,E_2481,F_2480),C_2477) = E_2481
      | ~ v1_funct_2(k1_tmap_1(A_2479,B_2482,C_2477,D_2478,E_2481,F_2480),k4_subset_1(A_2479,C_2477,D_2478),B_2482)
      | ~ v1_funct_1(k1_tmap_1(A_2479,B_2482,C_2477,D_2478,E_2481,F_2480))
      | k2_partfun1(D_2478,B_2482,F_2480,k9_subset_1(A_2479,C_2477,D_2478)) != k2_partfun1(C_2477,B_2482,E_2481,k9_subset_1(A_2479,C_2477,D_2478))
      | ~ m1_subset_1(F_2480,k1_zfmisc_1(k2_zfmisc_1(D_2478,B_2482)))
      | ~ v1_funct_2(F_2480,D_2478,B_2482)
      | ~ v1_funct_1(F_2480)
      | ~ m1_subset_1(E_2481,k1_zfmisc_1(k2_zfmisc_1(C_2477,B_2482)))
      | ~ v1_funct_2(E_2481,C_2477,B_2482)
      | ~ v1_funct_1(E_2481)
      | ~ m1_subset_1(D_2478,k1_zfmisc_1(A_2479))
      | v1_xboole_0(D_2478)
      | ~ m1_subset_1(C_2477,k1_zfmisc_1(A_2479))
      | v1_xboole_0(C_2477)
      | v1_xboole_0(B_2482)
      | v1_xboole_0(A_2479) ) ),
    inference(resolution,[status(thm)],[c_58,c_11488])).

tff(c_12713,plain,(
    ! [F_2563,E_2564,A_2562,B_2565,D_2561,C_2560] :
      ( k2_partfun1(k4_subset_1(A_2562,C_2560,D_2561),B_2565,k1_tmap_1(A_2562,B_2565,C_2560,D_2561,E_2564,F_2563),C_2560) = E_2564
      | ~ v1_funct_1(k1_tmap_1(A_2562,B_2565,C_2560,D_2561,E_2564,F_2563))
      | k2_partfun1(D_2561,B_2565,F_2563,k9_subset_1(A_2562,C_2560,D_2561)) != k2_partfun1(C_2560,B_2565,E_2564,k9_subset_1(A_2562,C_2560,D_2561))
      | ~ m1_subset_1(F_2563,k1_zfmisc_1(k2_zfmisc_1(D_2561,B_2565)))
      | ~ v1_funct_2(F_2563,D_2561,B_2565)
      | ~ v1_funct_1(F_2563)
      | ~ m1_subset_1(E_2564,k1_zfmisc_1(k2_zfmisc_1(C_2560,B_2565)))
      | ~ v1_funct_2(E_2564,C_2560,B_2565)
      | ~ v1_funct_1(E_2564)
      | ~ m1_subset_1(D_2561,k1_zfmisc_1(A_2562))
      | v1_xboole_0(D_2561)
      | ~ m1_subset_1(C_2560,k1_zfmisc_1(A_2562))
      | v1_xboole_0(C_2560)
      | v1_xboole_0(B_2565)
      | v1_xboole_0(A_2562) ) ),
    inference(resolution,[status(thm)],[c_60,c_12457])).

tff(c_12719,plain,(
    ! [A_2562,C_2560,E_2564] :
      ( k2_partfun1(k4_subset_1(A_2562,C_2560,'#skF_6'),'#skF_4',k1_tmap_1(A_2562,'#skF_4',C_2560,'#skF_6',E_2564,'#skF_8'),C_2560) = E_2564
      | ~ v1_funct_1(k1_tmap_1(A_2562,'#skF_4',C_2560,'#skF_6',E_2564,'#skF_8'))
      | k2_partfun1(C_2560,'#skF_4',E_2564,k9_subset_1(A_2562,C_2560,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_2562,C_2560,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_2564,k1_zfmisc_1(k2_zfmisc_1(C_2560,'#skF_4')))
      | ~ v1_funct_2(E_2564,C_2560,'#skF_4')
      | ~ v1_funct_1(E_2564)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2562))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_2560,k1_zfmisc_1(A_2562))
      | v1_xboole_0(C_2560)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2562) ) ),
    inference(resolution,[status(thm)],[c_66,c_12713])).

tff(c_12730,plain,(
    ! [A_2562,C_2560,E_2564] :
      ( k2_partfun1(k4_subset_1(A_2562,C_2560,'#skF_6'),'#skF_4',k1_tmap_1(A_2562,'#skF_4',C_2560,'#skF_6',E_2564,'#skF_8'),C_2560) = E_2564
      | ~ v1_funct_1(k1_tmap_1(A_2562,'#skF_4',C_2560,'#skF_6',E_2564,'#skF_8'))
      | k2_partfun1(C_2560,'#skF_4',E_2564,k9_subset_1(A_2562,C_2560,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2562,C_2560,'#skF_6'))
      | ~ m1_subset_1(E_2564,k1_zfmisc_1(k2_zfmisc_1(C_2560,'#skF_4')))
      | ~ v1_funct_2(E_2564,C_2560,'#skF_4')
      | ~ v1_funct_1(E_2564)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2562))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_2560,k1_zfmisc_1(A_2562))
      | v1_xboole_0(C_2560)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2562) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_10991,c_12719])).

tff(c_13416,plain,(
    ! [A_2636,C_2637,E_2638] :
      ( k2_partfun1(k4_subset_1(A_2636,C_2637,'#skF_6'),'#skF_4',k1_tmap_1(A_2636,'#skF_4',C_2637,'#skF_6',E_2638,'#skF_8'),C_2637) = E_2638
      | ~ v1_funct_1(k1_tmap_1(A_2636,'#skF_4',C_2637,'#skF_6',E_2638,'#skF_8'))
      | k2_partfun1(C_2637,'#skF_4',E_2638,k9_subset_1(A_2636,C_2637,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2636,C_2637,'#skF_6'))
      | ~ m1_subset_1(E_2638,k1_zfmisc_1(k2_zfmisc_1(C_2637,'#skF_4')))
      | ~ v1_funct_2(E_2638,C_2637,'#skF_4')
      | ~ v1_funct_1(E_2638)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2636))
      | ~ m1_subset_1(C_2637,k1_zfmisc_1(A_2636))
      | v1_xboole_0(C_2637)
      | v1_xboole_0(A_2636) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_12730])).

tff(c_13421,plain,(
    ! [A_2636] :
      ( k2_partfun1(k4_subset_1(A_2636,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_2636,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2636,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_2636,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2636,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2636))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2636))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_2636) ) ),
    inference(resolution,[status(thm)],[c_72,c_13416])).

tff(c_13432,plain,(
    ! [A_2636] :
      ( k2_partfun1(k4_subset_1(A_2636,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_2636,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2636,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2636,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2636,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2636))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2636))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_2636) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_10988,c_13421])).

tff(c_13465,plain,(
    ! [A_2644] :
      ( k2_partfun1(k4_subset_1(A_2644,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_2644,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2644,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2644,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2644,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2644))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2644))
      | v1_xboole_0(A_2644) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_13432])).

tff(c_7836,plain,(
    ! [A_1680,B_1681,C_1682] :
      ( r2_hidden('#skF_2'(A_1680,B_1681,C_1682),k1_relat_1(B_1681))
      | k7_relat_1(C_1682,A_1680) = B_1681
      | k3_xboole_0(k1_relat_1(C_1682),A_1680) != k1_relat_1(B_1681)
      | ~ v1_funct_1(C_1682)
      | ~ v1_relat_1(C_1682)
      | ~ v1_funct_1(B_1681)
      | ~ v1_relat_1(B_1681) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_7845,plain,(
    ! [A_1680,C_1682] :
      ( r2_hidden('#skF_2'(A_1680,k1_xboole_0,C_1682),k1_xboole_0)
      | k7_relat_1(C_1682,A_1680) = k1_xboole_0
      | k3_xboole_0(k1_relat_1(C_1682),A_1680) != k1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(C_1682)
      | ~ v1_relat_1(C_1682)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_7836])).

tff(c_7851,plain,(
    ! [A_1680,C_1682] :
      ( r2_hidden('#skF_2'(A_1680,k1_xboole_0,C_1682),k1_xboole_0)
      | k7_relat_1(C_1682,A_1680) = k1_xboole_0
      | k3_xboole_0(k1_relat_1(C_1682),A_1680) != k1_xboole_0
      | ~ v1_funct_1(C_1682)
      | ~ v1_relat_1(C_1682) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1499,c_7302,c_24,c_7845])).

tff(c_7853,plain,(
    ! [C_1683,A_1684] :
      ( k7_relat_1(C_1683,A_1684) = k1_xboole_0
      | k3_xboole_0(k1_relat_1(C_1683),A_1684) != k1_xboole_0
      | ~ v1_funct_1(C_1683)
      | ~ v1_relat_1(C_1683) ) ),
    inference(negUnitSimplification,[status(thm)],[c_7186,c_7851])).

tff(c_7874,plain,(
    ! [C_1685] :
      ( k7_relat_1(C_1685,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_1685)
      | ~ v1_relat_1(C_1685) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_7853])).

tff(c_7880,plain,
    ( k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1498,c_7874])).

tff(c_7889,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_7880])).

tff(c_7334,plain,(
    ! [A_1604,B_1605] :
      ( r1_xboole_0(A_1604,B_1605)
      | ~ r1_subset_1(A_1604,B_1605)
      | v1_xboole_0(B_1605)
      | v1_xboole_0(A_1604) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_7775,plain,(
    ! [A_1673,B_1674] :
      ( k3_xboole_0(A_1673,B_1674) = k1_xboole_0
      | ~ r1_subset_1(A_1673,B_1674)
      | v1_xboole_0(B_1674)
      | v1_xboole_0(A_1673) ) ),
    inference(resolution,[status(thm)],[c_7334,c_2])).

tff(c_7781,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_7775])).

tff(c_7785,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_82,c_7781])).

tff(c_7343,plain,(
    ! [A_1606,B_1607,C_1608] :
      ( k9_subset_1(A_1606,B_1607,C_1608) = k3_xboole_0(B_1607,C_1608)
      | ~ m1_subset_1(C_1608,k1_zfmisc_1(A_1606)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7356,plain,(
    ! [B_1607] : k9_subset_1('#skF_3',B_1607,'#skF_6') = k3_xboole_0(B_1607,'#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_7343])).

tff(c_7661,plain,(
    ! [A_1650,B_1651,C_1652,D_1653] :
      ( k2_partfun1(A_1650,B_1651,C_1652,D_1653) = k7_relat_1(C_1652,D_1653)
      | ~ m1_subset_1(C_1652,k1_zfmisc_1(k2_zfmisc_1(A_1650,B_1651)))
      | ~ v1_funct_1(C_1652) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_7663,plain,(
    ! [D_1653] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_1653) = k7_relat_1('#skF_7',D_1653)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_7661])).

tff(c_7671,plain,(
    ! [D_1653] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_1653) = k7_relat_1('#skF_7',D_1653) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7663])).

tff(c_7665,plain,(
    ! [D_1653] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_1653) = k7_relat_1('#skF_8',D_1653)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_66,c_7661])).

tff(c_7674,plain,(
    ! [D_1653] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_1653) = k7_relat_1('#skF_8',D_1653) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_7665])).

tff(c_7367,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k3_xboole_0('#skF_5','#skF_6')) = k2_partfun1('#skF_6','#skF_4','#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7356,c_7356,c_1475])).

tff(c_7831,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k7_relat_1('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7785,c_7785,c_7671,c_7674,c_7367])).

tff(c_7897,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7889,c_7831])).

tff(c_8018,plain,(
    ! [A_1697,E_1699,B_1700,C_1695,D_1696,F_1698] :
      ( v1_funct_1(k1_tmap_1(A_1697,B_1700,C_1695,D_1696,E_1699,F_1698))
      | ~ m1_subset_1(F_1698,k1_zfmisc_1(k2_zfmisc_1(D_1696,B_1700)))
      | ~ v1_funct_2(F_1698,D_1696,B_1700)
      | ~ v1_funct_1(F_1698)
      | ~ m1_subset_1(E_1699,k1_zfmisc_1(k2_zfmisc_1(C_1695,B_1700)))
      | ~ v1_funct_2(E_1699,C_1695,B_1700)
      | ~ v1_funct_1(E_1699)
      | ~ m1_subset_1(D_1696,k1_zfmisc_1(A_1697))
      | v1_xboole_0(D_1696)
      | ~ m1_subset_1(C_1695,k1_zfmisc_1(A_1697))
      | v1_xboole_0(C_1695)
      | v1_xboole_0(B_1700)
      | v1_xboole_0(A_1697) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_8022,plain,(
    ! [A_1697,C_1695,E_1699] :
      ( v1_funct_1(k1_tmap_1(A_1697,'#skF_4',C_1695,'#skF_6',E_1699,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_1699,k1_zfmisc_1(k2_zfmisc_1(C_1695,'#skF_4')))
      | ~ v1_funct_2(E_1699,C_1695,'#skF_4')
      | ~ v1_funct_1(E_1699)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1697))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1695,k1_zfmisc_1(A_1697))
      | v1_xboole_0(C_1695)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1697) ) ),
    inference(resolution,[status(thm)],[c_66,c_8018])).

tff(c_8032,plain,(
    ! [A_1697,C_1695,E_1699] :
      ( v1_funct_1(k1_tmap_1(A_1697,'#skF_4',C_1695,'#skF_6',E_1699,'#skF_8'))
      | ~ m1_subset_1(E_1699,k1_zfmisc_1(k2_zfmisc_1(C_1695,'#skF_4')))
      | ~ v1_funct_2(E_1699,C_1695,'#skF_4')
      | ~ v1_funct_1(E_1699)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1697))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1695,k1_zfmisc_1(A_1697))
      | v1_xboole_0(C_1695)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1697) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_8022])).

tff(c_8061,plain,(
    ! [A_1702,C_1703,E_1704] :
      ( v1_funct_1(k1_tmap_1(A_1702,'#skF_4',C_1703,'#skF_6',E_1704,'#skF_8'))
      | ~ m1_subset_1(E_1704,k1_zfmisc_1(k2_zfmisc_1(C_1703,'#skF_4')))
      | ~ v1_funct_2(E_1704,C_1703,'#skF_4')
      | ~ v1_funct_1(E_1704)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1702))
      | ~ m1_subset_1(C_1703,k1_zfmisc_1(A_1702))
      | v1_xboole_0(C_1703)
      | v1_xboole_0(A_1702) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_8032])).

tff(c_8063,plain,(
    ! [A_1702] :
      ( v1_funct_1(k1_tmap_1(A_1702,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1702))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1702))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1702) ) ),
    inference(resolution,[status(thm)],[c_72,c_8061])).

tff(c_8071,plain,(
    ! [A_1702] :
      ( v1_funct_1(k1_tmap_1(A_1702,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1702))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1702))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1702) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_8063])).

tff(c_8125,plain,(
    ! [A_1715] :
      ( v1_funct_1(k1_tmap_1(A_1715,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1715))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1715))
      | v1_xboole_0(A_1715) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_8071])).

tff(c_8128,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_8125])).

tff(c_8131,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_8128])).

tff(c_8132,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_8131])).

tff(c_8335,plain,(
    ! [A_1755,E_1754,B_1759,F_1758,D_1757,C_1756] :
      ( k2_partfun1(k4_subset_1(A_1755,C_1756,D_1757),B_1759,k1_tmap_1(A_1755,B_1759,C_1756,D_1757,E_1754,F_1758),D_1757) = F_1758
      | ~ m1_subset_1(k1_tmap_1(A_1755,B_1759,C_1756,D_1757,E_1754,F_1758),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1755,C_1756,D_1757),B_1759)))
      | ~ v1_funct_2(k1_tmap_1(A_1755,B_1759,C_1756,D_1757,E_1754,F_1758),k4_subset_1(A_1755,C_1756,D_1757),B_1759)
      | ~ v1_funct_1(k1_tmap_1(A_1755,B_1759,C_1756,D_1757,E_1754,F_1758))
      | k2_partfun1(D_1757,B_1759,F_1758,k9_subset_1(A_1755,C_1756,D_1757)) != k2_partfun1(C_1756,B_1759,E_1754,k9_subset_1(A_1755,C_1756,D_1757))
      | ~ m1_subset_1(F_1758,k1_zfmisc_1(k2_zfmisc_1(D_1757,B_1759)))
      | ~ v1_funct_2(F_1758,D_1757,B_1759)
      | ~ v1_funct_1(F_1758)
      | ~ m1_subset_1(E_1754,k1_zfmisc_1(k2_zfmisc_1(C_1756,B_1759)))
      | ~ v1_funct_2(E_1754,C_1756,B_1759)
      | ~ v1_funct_1(E_1754)
      | ~ m1_subset_1(D_1757,k1_zfmisc_1(A_1755))
      | v1_xboole_0(D_1757)
      | ~ m1_subset_1(C_1756,k1_zfmisc_1(A_1755))
      | v1_xboole_0(C_1756)
      | v1_xboole_0(B_1759)
      | v1_xboole_0(A_1755) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_9201,plain,(
    ! [D_1935,B_1939,F_1937,A_1936,E_1938,C_1934] :
      ( k2_partfun1(k4_subset_1(A_1936,C_1934,D_1935),B_1939,k1_tmap_1(A_1936,B_1939,C_1934,D_1935,E_1938,F_1937),D_1935) = F_1937
      | ~ v1_funct_2(k1_tmap_1(A_1936,B_1939,C_1934,D_1935,E_1938,F_1937),k4_subset_1(A_1936,C_1934,D_1935),B_1939)
      | ~ v1_funct_1(k1_tmap_1(A_1936,B_1939,C_1934,D_1935,E_1938,F_1937))
      | k2_partfun1(D_1935,B_1939,F_1937,k9_subset_1(A_1936,C_1934,D_1935)) != k2_partfun1(C_1934,B_1939,E_1938,k9_subset_1(A_1936,C_1934,D_1935))
      | ~ m1_subset_1(F_1937,k1_zfmisc_1(k2_zfmisc_1(D_1935,B_1939)))
      | ~ v1_funct_2(F_1937,D_1935,B_1939)
      | ~ v1_funct_1(F_1937)
      | ~ m1_subset_1(E_1938,k1_zfmisc_1(k2_zfmisc_1(C_1934,B_1939)))
      | ~ v1_funct_2(E_1938,C_1934,B_1939)
      | ~ v1_funct_1(E_1938)
      | ~ m1_subset_1(D_1935,k1_zfmisc_1(A_1936))
      | v1_xboole_0(D_1935)
      | ~ m1_subset_1(C_1934,k1_zfmisc_1(A_1936))
      | v1_xboole_0(C_1934)
      | v1_xboole_0(B_1939)
      | v1_xboole_0(A_1936) ) ),
    inference(resolution,[status(thm)],[c_58,c_8335])).

tff(c_9600,plain,(
    ! [C_2028,E_2032,D_2029,B_2033,F_2031,A_2030] :
      ( k2_partfun1(k4_subset_1(A_2030,C_2028,D_2029),B_2033,k1_tmap_1(A_2030,B_2033,C_2028,D_2029,E_2032,F_2031),D_2029) = F_2031
      | ~ v1_funct_1(k1_tmap_1(A_2030,B_2033,C_2028,D_2029,E_2032,F_2031))
      | k2_partfun1(D_2029,B_2033,F_2031,k9_subset_1(A_2030,C_2028,D_2029)) != k2_partfun1(C_2028,B_2033,E_2032,k9_subset_1(A_2030,C_2028,D_2029))
      | ~ m1_subset_1(F_2031,k1_zfmisc_1(k2_zfmisc_1(D_2029,B_2033)))
      | ~ v1_funct_2(F_2031,D_2029,B_2033)
      | ~ v1_funct_1(F_2031)
      | ~ m1_subset_1(E_2032,k1_zfmisc_1(k2_zfmisc_1(C_2028,B_2033)))
      | ~ v1_funct_2(E_2032,C_2028,B_2033)
      | ~ v1_funct_1(E_2032)
      | ~ m1_subset_1(D_2029,k1_zfmisc_1(A_2030))
      | v1_xboole_0(D_2029)
      | ~ m1_subset_1(C_2028,k1_zfmisc_1(A_2030))
      | v1_xboole_0(C_2028)
      | v1_xboole_0(B_2033)
      | v1_xboole_0(A_2030) ) ),
    inference(resolution,[status(thm)],[c_60,c_9201])).

tff(c_9606,plain,(
    ! [A_2030,C_2028,E_2032] :
      ( k2_partfun1(k4_subset_1(A_2030,C_2028,'#skF_6'),'#skF_4',k1_tmap_1(A_2030,'#skF_4',C_2028,'#skF_6',E_2032,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_2030,'#skF_4',C_2028,'#skF_6',E_2032,'#skF_8'))
      | k2_partfun1(C_2028,'#skF_4',E_2032,k9_subset_1(A_2030,C_2028,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_2030,C_2028,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_2032,k1_zfmisc_1(k2_zfmisc_1(C_2028,'#skF_4')))
      | ~ v1_funct_2(E_2032,C_2028,'#skF_4')
      | ~ v1_funct_1(E_2032)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2030))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_2028,k1_zfmisc_1(A_2030))
      | v1_xboole_0(C_2028)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2030) ) ),
    inference(resolution,[status(thm)],[c_66,c_9600])).

tff(c_9617,plain,(
    ! [A_2030,C_2028,E_2032] :
      ( k2_partfun1(k4_subset_1(A_2030,C_2028,'#skF_6'),'#skF_4',k1_tmap_1(A_2030,'#skF_4',C_2028,'#skF_6',E_2032,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_2030,'#skF_4',C_2028,'#skF_6',E_2032,'#skF_8'))
      | k2_partfun1(C_2028,'#skF_4',E_2032,k9_subset_1(A_2030,C_2028,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2030,C_2028,'#skF_6'))
      | ~ m1_subset_1(E_2032,k1_zfmisc_1(k2_zfmisc_1(C_2028,'#skF_4')))
      | ~ v1_funct_2(E_2032,C_2028,'#skF_4')
      | ~ v1_funct_1(E_2032)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2030))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_2028,k1_zfmisc_1(A_2030))
      | v1_xboole_0(C_2028)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2030) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_7674,c_9606])).

tff(c_10304,plain,(
    ! [A_2115,C_2116,E_2117] :
      ( k2_partfun1(k4_subset_1(A_2115,C_2116,'#skF_6'),'#skF_4',k1_tmap_1(A_2115,'#skF_4',C_2116,'#skF_6',E_2117,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_2115,'#skF_4',C_2116,'#skF_6',E_2117,'#skF_8'))
      | k2_partfun1(C_2116,'#skF_4',E_2117,k9_subset_1(A_2115,C_2116,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2115,C_2116,'#skF_6'))
      | ~ m1_subset_1(E_2117,k1_zfmisc_1(k2_zfmisc_1(C_2116,'#skF_4')))
      | ~ v1_funct_2(E_2117,C_2116,'#skF_4')
      | ~ v1_funct_1(E_2117)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2115))
      | ~ m1_subset_1(C_2116,k1_zfmisc_1(A_2115))
      | v1_xboole_0(C_2116)
      | v1_xboole_0(A_2115) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_9617])).

tff(c_10309,plain,(
    ! [A_2115] :
      ( k2_partfun1(k4_subset_1(A_2115,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_2115,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_2115,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_2115,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2115,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2115))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2115))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_2115) ) ),
    inference(resolution,[status(thm)],[c_72,c_10304])).

tff(c_10320,plain,(
    ! [A_2115] :
      ( k2_partfun1(k4_subset_1(A_2115,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_2115,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_2115,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2115,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2115,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2115))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2115))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_2115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_7671,c_10309])).

tff(c_10466,plain,(
    ! [A_2139] :
      ( k2_partfun1(k4_subset_1(A_2139,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_2139,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_2139,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2139,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2139,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2139))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2139))
      | v1_xboole_0(A_2139) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_10320])).

tff(c_1474,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_7303,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1474])).

tff(c_10477,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10466,c_7303])).

tff(c_10491,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_7889,c_7785,c_7356,c_7897,c_7785,c_7356,c_8132,c_10477])).

tff(c_10493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_10491])).

tff(c_10494,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1474])).

tff(c_13474,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13465,c_10494])).

tff(c_13485,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_11137,c_11033,c_10548,c_11145,c_11033,c_10548,c_11380,c_13474])).

tff(c_13487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_13485])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 16:35:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.36/5.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.49/5.21  
% 12.49/5.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.49/5.21  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4 > #skF_1
% 12.49/5.21  
% 12.49/5.21  %Foreground sorts:
% 12.49/5.21  
% 12.49/5.21  
% 12.49/5.21  %Background operators:
% 12.49/5.21  
% 12.49/5.21  
% 12.49/5.21  %Foreground operators:
% 12.49/5.21  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 12.49/5.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.49/5.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.49/5.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.49/5.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.49/5.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.49/5.21  tff('#skF_7', type, '#skF_7': $i).
% 12.49/5.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.49/5.21  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 12.49/5.21  tff('#skF_5', type, '#skF_5': $i).
% 12.49/5.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.49/5.21  tff('#skF_6', type, '#skF_6': $i).
% 12.49/5.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.49/5.21  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 12.49/5.21  tff('#skF_3', type, '#skF_3': $i).
% 12.49/5.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.49/5.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.49/5.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.49/5.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.49/5.21  tff('#skF_8', type, '#skF_8': $i).
% 12.49/5.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.49/5.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.49/5.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.49/5.21  tff('#skF_4', type, '#skF_4': $i).
% 12.49/5.21  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.49/5.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.49/5.21  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 12.49/5.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.49/5.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.49/5.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.49/5.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.49/5.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.49/5.21  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 12.49/5.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.49/5.21  
% 12.49/5.24  tff(f_268, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 12.49/5.24  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.49/5.24  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 12.49/5.24  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 12.49/5.24  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 12.49/5.24  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 12.49/5.24  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_funct_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 12.49/5.24  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 12.49/5.24  tff(f_106, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = k3_xboole_0(k1_relat_1(C), A)) & (![D]: (r2_hidden(D, k1_relat_1(B)) => (k1_funct_1(B, D) = k1_funct_1(C, D))))) => (B = k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_funct_1)).
% 12.49/5.25  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 12.49/5.25  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 12.49/5.25  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 12.49/5.25  tff(f_144, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 12.49/5.25  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.49/5.25  tff(f_138, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 12.49/5.25  tff(f_130, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 12.49/5.25  tff(f_226, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 12.49/5.25  tff(f_192, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 12.49/5.25  tff(c_90, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_268])).
% 12.49/5.25  tff(c_84, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_268])).
% 12.49/5.25  tff(c_80, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_268])).
% 12.49/5.25  tff(c_70, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_268])).
% 12.49/5.25  tff(c_66, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_268])).
% 12.49/5.25  tff(c_1486, plain, (![C_460, A_461, B_462]: (v1_relat_1(C_460) | ~m1_subset_1(C_460, k1_zfmisc_1(k2_zfmisc_1(A_461, B_462))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 12.49/5.25  tff(c_1498, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_66, c_1486])).
% 12.49/5.25  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.49/5.25  tff(c_12, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.49/5.25  tff(c_7181, plain, (![A_1574, B_1575, C_1576]: (~r1_xboole_0(A_1574, B_1575) | ~r2_hidden(C_1576, k3_xboole_0(A_1574, B_1575)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.49/5.25  tff(c_7184, plain, (![A_8, C_1576]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_1576, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_7181])).
% 12.49/5.25  tff(c_7186, plain, (![C_1576]: (~r2_hidden(C_1576, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_7184])).
% 12.49/5.25  tff(c_16, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.49/5.25  tff(c_1499, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_1486])).
% 12.49/5.25  tff(c_7246, plain, (![B_1589, A_1590]: (v1_funct_1(B_1589) | ~m1_subset_1(B_1589, k1_zfmisc_1(A_1590)) | ~v1_funct_1(A_1590) | ~v1_relat_1(A_1590))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.49/5.25  tff(c_7267, plain, (![A_13]: (v1_funct_1(k1_xboole_0) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(resolution, [status(thm)], [c_16, c_7246])).
% 12.49/5.25  tff(c_7287, plain, (![A_1594]: (~v1_funct_1(A_1594) | ~v1_relat_1(A_1594))), inference(splitLeft, [status(thm)], [c_7267])).
% 12.49/5.25  tff(c_7293, plain, (~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_1498, c_7287])).
% 12.49/5.25  tff(c_7301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_7293])).
% 12.49/5.25  tff(c_7302, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_7267])).
% 12.49/5.25  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 12.49/5.25  tff(c_11084, plain, (![A_2226, B_2227, C_2228]: (r2_hidden('#skF_2'(A_2226, B_2227, C_2228), k1_relat_1(B_2227)) | k7_relat_1(C_2228, A_2226)=B_2227 | k3_xboole_0(k1_relat_1(C_2228), A_2226)!=k1_relat_1(B_2227) | ~v1_funct_1(C_2228) | ~v1_relat_1(C_2228) | ~v1_funct_1(B_2227) | ~v1_relat_1(B_2227))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.49/5.25  tff(c_11093, plain, (![A_2226, C_2228]: (r2_hidden('#skF_2'(A_2226, k1_xboole_0, C_2228), k1_xboole_0) | k7_relat_1(C_2228, A_2226)=k1_xboole_0 | k3_xboole_0(k1_relat_1(C_2228), A_2226)!=k1_relat_1(k1_xboole_0) | ~v1_funct_1(C_2228) | ~v1_relat_1(C_2228) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_11084])).
% 12.49/5.25  tff(c_11099, plain, (![A_2226, C_2228]: (r2_hidden('#skF_2'(A_2226, k1_xboole_0, C_2228), k1_xboole_0) | k7_relat_1(C_2228, A_2226)=k1_xboole_0 | k3_xboole_0(k1_relat_1(C_2228), A_2226)!=k1_xboole_0 | ~v1_funct_1(C_2228) | ~v1_relat_1(C_2228))), inference(demodulation, [status(thm), theory('equality')], [c_1499, c_7302, c_24, c_11093])).
% 12.49/5.25  tff(c_11101, plain, (![C_2229, A_2230]: (k7_relat_1(C_2229, A_2230)=k1_xboole_0 | k3_xboole_0(k1_relat_1(C_2229), A_2230)!=k1_xboole_0 | ~v1_funct_1(C_2229) | ~v1_relat_1(C_2229))), inference(negUnitSimplification, [status(thm)], [c_7186, c_11099])).
% 12.49/5.25  tff(c_11122, plain, (![C_2231]: (k7_relat_1(C_2231, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_2231) | ~v1_relat_1(C_2231))), inference(superposition, [status(thm), theory('equality')], [c_10, c_11101])).
% 12.49/5.25  tff(c_11128, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_1498, c_11122])).
% 12.49/5.25  tff(c_11137, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_11128])).
% 12.49/5.25  tff(c_86, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_268])).
% 12.49/5.25  tff(c_82, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_268])).
% 12.49/5.25  tff(c_78, plain, (r1_subset_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_268])).
% 12.49/5.25  tff(c_10526, plain, (![A_2149, B_2150]: (r1_xboole_0(A_2149, B_2150) | ~r1_subset_1(A_2149, B_2150) | v1_xboole_0(B_2150) | v1_xboole_0(A_2149))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.49/5.25  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.49/5.25  tff(c_11023, plain, (![A_2219, B_2220]: (k3_xboole_0(A_2219, B_2220)=k1_xboole_0 | ~r1_subset_1(A_2219, B_2220) | v1_xboole_0(B_2220) | v1_xboole_0(A_2219))), inference(resolution, [status(thm)], [c_10526, c_2])).
% 12.49/5.25  tff(c_11029, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_78, c_11023])).
% 12.49/5.25  tff(c_11033, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_82, c_11029])).
% 12.49/5.25  tff(c_10535, plain, (![A_2151, B_2152, C_2153]: (k9_subset_1(A_2151, B_2152, C_2153)=k3_xboole_0(B_2152, C_2153) | ~m1_subset_1(C_2153, k1_zfmisc_1(A_2151)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.49/5.25  tff(c_10548, plain, (![B_2152]: (k9_subset_1('#skF_3', B_2152, '#skF_6')=k3_xboole_0(B_2152, '#skF_6'))), inference(resolution, [status(thm)], [c_80, c_10535])).
% 12.49/5.25  tff(c_10978, plain, (![A_2210, B_2211, C_2212, D_2213]: (k2_partfun1(A_2210, B_2211, C_2212, D_2213)=k7_relat_1(C_2212, D_2213) | ~m1_subset_1(C_2212, k1_zfmisc_1(k2_zfmisc_1(A_2210, B_2211))) | ~v1_funct_1(C_2212))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.49/5.25  tff(c_10982, plain, (![D_2213]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_2213)=k7_relat_1('#skF_8', D_2213) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_66, c_10978])).
% 12.49/5.25  tff(c_10991, plain, (![D_2213]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_2213)=k7_relat_1('#skF_8', D_2213))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_10982])).
% 12.49/5.25  tff(c_76, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_268])).
% 12.49/5.25  tff(c_72, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_268])).
% 12.49/5.25  tff(c_10980, plain, (![D_2213]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_2213)=k7_relat_1('#skF_7', D_2213) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_72, c_10978])).
% 12.49/5.25  tff(c_10988, plain, (![D_2213]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_2213)=k7_relat_1('#skF_7', D_2213))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_10980])).
% 12.49/5.25  tff(c_120, plain, (![C_245, A_246, B_247]: (v1_relat_1(C_245) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 12.49/5.25  tff(c_131, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_72, c_120])).
% 12.49/5.25  tff(c_88, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_268])).
% 12.49/5.25  tff(c_776, plain, (![C_352, A_353, B_354]: (v4_relat_1(C_352, A_353) | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 12.49/5.25  tff(c_787, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_72, c_776])).
% 12.49/5.25  tff(c_895, plain, (![B_373, A_374]: (k1_relat_1(B_373)=A_374 | ~v1_partfun1(B_373, A_374) | ~v4_relat_1(B_373, A_374) | ~v1_relat_1(B_373))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.49/5.25  tff(c_904, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_787, c_895])).
% 12.49/5.25  tff(c_913, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_904])).
% 12.49/5.25  tff(c_914, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_913])).
% 12.49/5.25  tff(c_74, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_268])).
% 12.49/5.25  tff(c_1034, plain, (![C_396, A_397, B_398]: (v1_partfun1(C_396, A_397) | ~v1_funct_2(C_396, A_397, B_398) | ~v1_funct_1(C_396) | ~m1_subset_1(C_396, k1_zfmisc_1(k2_zfmisc_1(A_397, B_398))) | v1_xboole_0(B_398))), inference(cnfTransformation, [status(thm)], [f_130])).
% 12.49/5.25  tff(c_1037, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_1034])).
% 12.49/5.25  tff(c_1047, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1037])).
% 12.49/5.25  tff(c_1049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_914, c_1047])).
% 12.49/5.25  tff(c_1050, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_913])).
% 12.49/5.25  tff(c_753, plain, (![A_344, B_345, C_346]: (~r1_xboole_0(A_344, B_345) | ~r2_hidden(C_346, k3_xboole_0(A_344, B_345)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.49/5.25  tff(c_756, plain, (![A_8, C_346]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_346, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_753])).
% 12.49/5.25  tff(c_758, plain, (![C_346]: (~r2_hidden(C_346, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_756])).
% 12.49/5.25  tff(c_133, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_120])).
% 12.49/5.25  tff(c_132, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_66, c_120])).
% 12.49/5.25  tff(c_825, plain, (![B_366, A_367]: (v1_funct_1(B_366) | ~m1_subset_1(B_366, k1_zfmisc_1(A_367)) | ~v1_funct_1(A_367) | ~v1_relat_1(A_367))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.49/5.25  tff(c_846, plain, (![A_13]: (v1_funct_1(k1_xboole_0) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(resolution, [status(thm)], [c_16, c_825])).
% 12.49/5.25  tff(c_850, plain, (![A_368]: (~v1_funct_1(A_368) | ~v1_relat_1(A_368))), inference(splitLeft, [status(thm)], [c_846])).
% 12.49/5.25  tff(c_856, plain, (~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_132, c_850])).
% 12.49/5.25  tff(c_864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_856])).
% 12.49/5.25  tff(c_865, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_846])).
% 12.49/5.25  tff(c_1404, plain, (![A_451, B_452, C_453]: (r2_hidden('#skF_2'(A_451, B_452, C_453), k1_relat_1(B_452)) | k7_relat_1(C_453, A_451)=B_452 | k3_xboole_0(k1_relat_1(C_453), A_451)!=k1_relat_1(B_452) | ~v1_funct_1(C_453) | ~v1_relat_1(C_453) | ~v1_funct_1(B_452) | ~v1_relat_1(B_452))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.49/5.25  tff(c_1413, plain, (![A_451, C_453]: (r2_hidden('#skF_2'(A_451, k1_xboole_0, C_453), k1_xboole_0) | k7_relat_1(C_453, A_451)=k1_xboole_0 | k3_xboole_0(k1_relat_1(C_453), A_451)!=k1_relat_1(k1_xboole_0) | ~v1_funct_1(C_453) | ~v1_relat_1(C_453) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1404])).
% 12.49/5.25  tff(c_1419, plain, (![A_451, C_453]: (r2_hidden('#skF_2'(A_451, k1_xboole_0, C_453), k1_xboole_0) | k7_relat_1(C_453, A_451)=k1_xboole_0 | k3_xboole_0(k1_relat_1(C_453), A_451)!=k1_xboole_0 | ~v1_funct_1(C_453) | ~v1_relat_1(C_453))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_865, c_24, c_1413])).
% 12.49/5.25  tff(c_1421, plain, (![C_454, A_455]: (k7_relat_1(C_454, A_455)=k1_xboole_0 | k3_xboole_0(k1_relat_1(C_454), A_455)!=k1_xboole_0 | ~v1_funct_1(C_454) | ~v1_relat_1(C_454))), inference(negUnitSimplification, [status(thm)], [c_758, c_1419])).
% 12.49/5.25  tff(c_1427, plain, (![A_455]: (k7_relat_1('#skF_7', A_455)=k1_xboole_0 | k3_xboole_0('#skF_5', A_455)!=k1_xboole_0 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1050, c_1421])).
% 12.49/5.25  tff(c_1442, plain, (![A_456]: (k7_relat_1('#skF_7', A_456)=k1_xboole_0 | k3_xboole_0('#skF_5', A_456)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_76, c_1427])).
% 12.49/5.25  tff(c_791, plain, (![A_356, B_357]: (r1_xboole_0(A_356, B_357) | ~r1_subset_1(A_356, B_357) | v1_xboole_0(B_357) | v1_xboole_0(A_356))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.49/5.25  tff(c_1346, plain, (![A_442, B_443]: (k3_xboole_0(A_442, B_443)=k1_xboole_0 | ~r1_subset_1(A_442, B_443) | v1_xboole_0(B_443) | v1_xboole_0(A_442))), inference(resolution, [status(thm)], [c_791, c_2])).
% 12.49/5.25  tff(c_1349, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_78, c_1346])).
% 12.49/5.25  tff(c_1352, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_82, c_1349])).
% 12.49/5.25  tff(c_1293, plain, (![A_432, B_433, C_434, D_435]: (k2_partfun1(A_432, B_433, C_434, D_435)=k7_relat_1(C_434, D_435) | ~m1_subset_1(C_434, k1_zfmisc_1(k2_zfmisc_1(A_432, B_433))) | ~v1_funct_1(C_434))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.49/5.25  tff(c_1297, plain, (![D_435]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_435)=k7_relat_1('#skF_8', D_435) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_66, c_1293])).
% 12.49/5.25  tff(c_1306, plain, (![D_435]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_435)=k7_relat_1('#skF_8', D_435))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1297])).
% 12.49/5.25  tff(c_1295, plain, (![D_435]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_435)=k7_relat_1('#skF_7', D_435) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_72, c_1293])).
% 12.49/5.25  tff(c_1303, plain, (![D_435]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_435)=k7_relat_1('#skF_7', D_435))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1295])).
% 12.49/5.25  tff(c_1235, plain, (![A_423, B_424, C_425]: (k9_subset_1(A_423, B_424, C_425)=k3_xboole_0(B_424, C_425) | ~m1_subset_1(C_425, k1_zfmisc_1(A_423)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.49/5.25  tff(c_1248, plain, (![B_424]: (k9_subset_1('#skF_3', B_424, '#skF_6')=k3_xboole_0(B_424, '#skF_6'))), inference(resolution, [status(thm)], [c_80, c_1235])).
% 12.49/5.25  tff(c_64, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_268])).
% 12.49/5.25  tff(c_109, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_64])).
% 12.49/5.25  tff(c_1265, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k3_xboole_0('#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1248, c_1248, c_109])).
% 12.49/5.25  tff(c_1380, plain, (k7_relat_1('#skF_7', k1_xboole_0)!=k7_relat_1('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1352, c_1352, c_1306, c_1303, c_1265])).
% 12.49/5.25  tff(c_1448, plain, (k7_relat_1('#skF_8', k1_xboole_0)!=k1_xboole_0 | k3_xboole_0('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1442, c_1380])).
% 12.49/5.25  tff(c_1454, plain, (k7_relat_1('#skF_8', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1448])).
% 12.49/5.25  tff(c_1456, plain, (![C_457]: (k7_relat_1(C_457, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_457) | ~v1_relat_1(C_457))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1421])).
% 12.49/5.25  tff(c_1462, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_132, c_1456])).
% 12.49/5.25  tff(c_1471, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1462])).
% 12.49/5.25  tff(c_1473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1454, c_1471])).
% 12.49/5.25  tff(c_1475, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_64])).
% 12.49/5.25  tff(c_10559, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k3_xboole_0('#skF_5', '#skF_6'))=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_10548, c_10548, c_1475])).
% 12.49/5.25  tff(c_10995, plain, (k2_partfun1('#skF_6', '#skF_4', '#skF_8', k3_xboole_0('#skF_5', '#skF_6'))=k7_relat_1('#skF_7', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_10988, c_10559])).
% 12.49/5.25  tff(c_11079, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k7_relat_1('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_11033, c_11033, c_10991, c_10995])).
% 12.49/5.25  tff(c_11145, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11137, c_11079])).
% 12.49/5.25  tff(c_68, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_268])).
% 12.49/5.25  tff(c_11266, plain, (![E_2245, D_2242, A_2243, F_2244, C_2241, B_2246]: (v1_funct_1(k1_tmap_1(A_2243, B_2246, C_2241, D_2242, E_2245, F_2244)) | ~m1_subset_1(F_2244, k1_zfmisc_1(k2_zfmisc_1(D_2242, B_2246))) | ~v1_funct_2(F_2244, D_2242, B_2246) | ~v1_funct_1(F_2244) | ~m1_subset_1(E_2245, k1_zfmisc_1(k2_zfmisc_1(C_2241, B_2246))) | ~v1_funct_2(E_2245, C_2241, B_2246) | ~v1_funct_1(E_2245) | ~m1_subset_1(D_2242, k1_zfmisc_1(A_2243)) | v1_xboole_0(D_2242) | ~m1_subset_1(C_2241, k1_zfmisc_1(A_2243)) | v1_xboole_0(C_2241) | v1_xboole_0(B_2246) | v1_xboole_0(A_2243))), inference(cnfTransformation, [status(thm)], [f_226])).
% 12.49/5.25  tff(c_11270, plain, (![A_2243, C_2241, E_2245]: (v1_funct_1(k1_tmap_1(A_2243, '#skF_4', C_2241, '#skF_6', E_2245, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_2245, k1_zfmisc_1(k2_zfmisc_1(C_2241, '#skF_4'))) | ~v1_funct_2(E_2245, C_2241, '#skF_4') | ~v1_funct_1(E_2245) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2243)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_2241, k1_zfmisc_1(A_2243)) | v1_xboole_0(C_2241) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2243))), inference(resolution, [status(thm)], [c_66, c_11266])).
% 12.49/5.25  tff(c_11280, plain, (![A_2243, C_2241, E_2245]: (v1_funct_1(k1_tmap_1(A_2243, '#skF_4', C_2241, '#skF_6', E_2245, '#skF_8')) | ~m1_subset_1(E_2245, k1_zfmisc_1(k2_zfmisc_1(C_2241, '#skF_4'))) | ~v1_funct_2(E_2245, C_2241, '#skF_4') | ~v1_funct_1(E_2245) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2243)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_2241, k1_zfmisc_1(A_2243)) | v1_xboole_0(C_2241) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2243))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_11270])).
% 12.49/5.25  tff(c_11309, plain, (![A_2248, C_2249, E_2250]: (v1_funct_1(k1_tmap_1(A_2248, '#skF_4', C_2249, '#skF_6', E_2250, '#skF_8')) | ~m1_subset_1(E_2250, k1_zfmisc_1(k2_zfmisc_1(C_2249, '#skF_4'))) | ~v1_funct_2(E_2250, C_2249, '#skF_4') | ~v1_funct_1(E_2250) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2248)) | ~m1_subset_1(C_2249, k1_zfmisc_1(A_2248)) | v1_xboole_0(C_2249) | v1_xboole_0(A_2248))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_11280])).
% 12.49/5.25  tff(c_11311, plain, (![A_2248]: (v1_funct_1(k1_tmap_1(A_2248, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2248)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2248)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_2248))), inference(resolution, [status(thm)], [c_72, c_11309])).
% 12.49/5.25  tff(c_11319, plain, (![A_2248]: (v1_funct_1(k1_tmap_1(A_2248, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2248)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2248)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_2248))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_11311])).
% 12.49/5.25  tff(c_11373, plain, (![A_2261]: (v1_funct_1(k1_tmap_1(A_2261, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2261)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2261)) | v1_xboole_0(A_2261))), inference(negUnitSimplification, [status(thm)], [c_86, c_11319])).
% 12.49/5.25  tff(c_11376, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_84, c_11373])).
% 12.49/5.25  tff(c_11379, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_11376])).
% 12.49/5.25  tff(c_11380, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_90, c_11379])).
% 12.49/5.25  tff(c_60, plain, (![C_177, F_180, A_175, D_178, B_176, E_179]: (v1_funct_2(k1_tmap_1(A_175, B_176, C_177, D_178, E_179, F_180), k4_subset_1(A_175, C_177, D_178), B_176) | ~m1_subset_1(F_180, k1_zfmisc_1(k2_zfmisc_1(D_178, B_176))) | ~v1_funct_2(F_180, D_178, B_176) | ~v1_funct_1(F_180) | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(C_177, B_176))) | ~v1_funct_2(E_179, C_177, B_176) | ~v1_funct_1(E_179) | ~m1_subset_1(D_178, k1_zfmisc_1(A_175)) | v1_xboole_0(D_178) | ~m1_subset_1(C_177, k1_zfmisc_1(A_175)) | v1_xboole_0(C_177) | v1_xboole_0(B_176) | v1_xboole_0(A_175))), inference(cnfTransformation, [status(thm)], [f_226])).
% 12.49/5.25  tff(c_58, plain, (![C_177, F_180, A_175, D_178, B_176, E_179]: (m1_subset_1(k1_tmap_1(A_175, B_176, C_177, D_178, E_179, F_180), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_175, C_177, D_178), B_176))) | ~m1_subset_1(F_180, k1_zfmisc_1(k2_zfmisc_1(D_178, B_176))) | ~v1_funct_2(F_180, D_178, B_176) | ~v1_funct_1(F_180) | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(C_177, B_176))) | ~v1_funct_2(E_179, C_177, B_176) | ~v1_funct_1(E_179) | ~m1_subset_1(D_178, k1_zfmisc_1(A_175)) | v1_xboole_0(D_178) | ~m1_subset_1(C_177, k1_zfmisc_1(A_175)) | v1_xboole_0(C_177) | v1_xboole_0(B_176) | v1_xboole_0(A_175))), inference(cnfTransformation, [status(thm)], [f_226])).
% 12.49/5.25  tff(c_11488, plain, (![D_2285, E_2282, B_2287, A_2283, C_2284, F_2286]: (k2_partfun1(k4_subset_1(A_2283, C_2284, D_2285), B_2287, k1_tmap_1(A_2283, B_2287, C_2284, D_2285, E_2282, F_2286), C_2284)=E_2282 | ~m1_subset_1(k1_tmap_1(A_2283, B_2287, C_2284, D_2285, E_2282, F_2286), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2283, C_2284, D_2285), B_2287))) | ~v1_funct_2(k1_tmap_1(A_2283, B_2287, C_2284, D_2285, E_2282, F_2286), k4_subset_1(A_2283, C_2284, D_2285), B_2287) | ~v1_funct_1(k1_tmap_1(A_2283, B_2287, C_2284, D_2285, E_2282, F_2286)) | k2_partfun1(D_2285, B_2287, F_2286, k9_subset_1(A_2283, C_2284, D_2285))!=k2_partfun1(C_2284, B_2287, E_2282, k9_subset_1(A_2283, C_2284, D_2285)) | ~m1_subset_1(F_2286, k1_zfmisc_1(k2_zfmisc_1(D_2285, B_2287))) | ~v1_funct_2(F_2286, D_2285, B_2287) | ~v1_funct_1(F_2286) | ~m1_subset_1(E_2282, k1_zfmisc_1(k2_zfmisc_1(C_2284, B_2287))) | ~v1_funct_2(E_2282, C_2284, B_2287) | ~v1_funct_1(E_2282) | ~m1_subset_1(D_2285, k1_zfmisc_1(A_2283)) | v1_xboole_0(D_2285) | ~m1_subset_1(C_2284, k1_zfmisc_1(A_2283)) | v1_xboole_0(C_2284) | v1_xboole_0(B_2287) | v1_xboole_0(A_2283))), inference(cnfTransformation, [status(thm)], [f_192])).
% 12.49/5.25  tff(c_12457, plain, (![A_2479, D_2478, B_2482, E_2481, F_2480, C_2477]: (k2_partfun1(k4_subset_1(A_2479, C_2477, D_2478), B_2482, k1_tmap_1(A_2479, B_2482, C_2477, D_2478, E_2481, F_2480), C_2477)=E_2481 | ~v1_funct_2(k1_tmap_1(A_2479, B_2482, C_2477, D_2478, E_2481, F_2480), k4_subset_1(A_2479, C_2477, D_2478), B_2482) | ~v1_funct_1(k1_tmap_1(A_2479, B_2482, C_2477, D_2478, E_2481, F_2480)) | k2_partfun1(D_2478, B_2482, F_2480, k9_subset_1(A_2479, C_2477, D_2478))!=k2_partfun1(C_2477, B_2482, E_2481, k9_subset_1(A_2479, C_2477, D_2478)) | ~m1_subset_1(F_2480, k1_zfmisc_1(k2_zfmisc_1(D_2478, B_2482))) | ~v1_funct_2(F_2480, D_2478, B_2482) | ~v1_funct_1(F_2480) | ~m1_subset_1(E_2481, k1_zfmisc_1(k2_zfmisc_1(C_2477, B_2482))) | ~v1_funct_2(E_2481, C_2477, B_2482) | ~v1_funct_1(E_2481) | ~m1_subset_1(D_2478, k1_zfmisc_1(A_2479)) | v1_xboole_0(D_2478) | ~m1_subset_1(C_2477, k1_zfmisc_1(A_2479)) | v1_xboole_0(C_2477) | v1_xboole_0(B_2482) | v1_xboole_0(A_2479))), inference(resolution, [status(thm)], [c_58, c_11488])).
% 12.49/5.25  tff(c_12713, plain, (![F_2563, E_2564, A_2562, B_2565, D_2561, C_2560]: (k2_partfun1(k4_subset_1(A_2562, C_2560, D_2561), B_2565, k1_tmap_1(A_2562, B_2565, C_2560, D_2561, E_2564, F_2563), C_2560)=E_2564 | ~v1_funct_1(k1_tmap_1(A_2562, B_2565, C_2560, D_2561, E_2564, F_2563)) | k2_partfun1(D_2561, B_2565, F_2563, k9_subset_1(A_2562, C_2560, D_2561))!=k2_partfun1(C_2560, B_2565, E_2564, k9_subset_1(A_2562, C_2560, D_2561)) | ~m1_subset_1(F_2563, k1_zfmisc_1(k2_zfmisc_1(D_2561, B_2565))) | ~v1_funct_2(F_2563, D_2561, B_2565) | ~v1_funct_1(F_2563) | ~m1_subset_1(E_2564, k1_zfmisc_1(k2_zfmisc_1(C_2560, B_2565))) | ~v1_funct_2(E_2564, C_2560, B_2565) | ~v1_funct_1(E_2564) | ~m1_subset_1(D_2561, k1_zfmisc_1(A_2562)) | v1_xboole_0(D_2561) | ~m1_subset_1(C_2560, k1_zfmisc_1(A_2562)) | v1_xboole_0(C_2560) | v1_xboole_0(B_2565) | v1_xboole_0(A_2562))), inference(resolution, [status(thm)], [c_60, c_12457])).
% 12.49/5.25  tff(c_12719, plain, (![A_2562, C_2560, E_2564]: (k2_partfun1(k4_subset_1(A_2562, C_2560, '#skF_6'), '#skF_4', k1_tmap_1(A_2562, '#skF_4', C_2560, '#skF_6', E_2564, '#skF_8'), C_2560)=E_2564 | ~v1_funct_1(k1_tmap_1(A_2562, '#skF_4', C_2560, '#skF_6', E_2564, '#skF_8')) | k2_partfun1(C_2560, '#skF_4', E_2564, k9_subset_1(A_2562, C_2560, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_2562, C_2560, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_2564, k1_zfmisc_1(k2_zfmisc_1(C_2560, '#skF_4'))) | ~v1_funct_2(E_2564, C_2560, '#skF_4') | ~v1_funct_1(E_2564) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2562)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_2560, k1_zfmisc_1(A_2562)) | v1_xboole_0(C_2560) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2562))), inference(resolution, [status(thm)], [c_66, c_12713])).
% 12.49/5.25  tff(c_12730, plain, (![A_2562, C_2560, E_2564]: (k2_partfun1(k4_subset_1(A_2562, C_2560, '#skF_6'), '#skF_4', k1_tmap_1(A_2562, '#skF_4', C_2560, '#skF_6', E_2564, '#skF_8'), C_2560)=E_2564 | ~v1_funct_1(k1_tmap_1(A_2562, '#skF_4', C_2560, '#skF_6', E_2564, '#skF_8')) | k2_partfun1(C_2560, '#skF_4', E_2564, k9_subset_1(A_2562, C_2560, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2562, C_2560, '#skF_6')) | ~m1_subset_1(E_2564, k1_zfmisc_1(k2_zfmisc_1(C_2560, '#skF_4'))) | ~v1_funct_2(E_2564, C_2560, '#skF_4') | ~v1_funct_1(E_2564) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2562)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_2560, k1_zfmisc_1(A_2562)) | v1_xboole_0(C_2560) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2562))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_10991, c_12719])).
% 12.49/5.25  tff(c_13416, plain, (![A_2636, C_2637, E_2638]: (k2_partfun1(k4_subset_1(A_2636, C_2637, '#skF_6'), '#skF_4', k1_tmap_1(A_2636, '#skF_4', C_2637, '#skF_6', E_2638, '#skF_8'), C_2637)=E_2638 | ~v1_funct_1(k1_tmap_1(A_2636, '#skF_4', C_2637, '#skF_6', E_2638, '#skF_8')) | k2_partfun1(C_2637, '#skF_4', E_2638, k9_subset_1(A_2636, C_2637, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2636, C_2637, '#skF_6')) | ~m1_subset_1(E_2638, k1_zfmisc_1(k2_zfmisc_1(C_2637, '#skF_4'))) | ~v1_funct_2(E_2638, C_2637, '#skF_4') | ~v1_funct_1(E_2638) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2636)) | ~m1_subset_1(C_2637, k1_zfmisc_1(A_2636)) | v1_xboole_0(C_2637) | v1_xboole_0(A_2636))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_12730])).
% 12.49/5.25  tff(c_13421, plain, (![A_2636]: (k2_partfun1(k4_subset_1(A_2636, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_2636, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2636, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_2636, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2636, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2636)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2636)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_2636))), inference(resolution, [status(thm)], [c_72, c_13416])).
% 12.49/5.25  tff(c_13432, plain, (![A_2636]: (k2_partfun1(k4_subset_1(A_2636, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_2636, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2636, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_2636, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2636, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2636)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2636)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_2636))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_10988, c_13421])).
% 12.49/5.25  tff(c_13465, plain, (![A_2644]: (k2_partfun1(k4_subset_1(A_2644, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_2644, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2644, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_2644, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2644, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2644)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2644)) | v1_xboole_0(A_2644))), inference(negUnitSimplification, [status(thm)], [c_86, c_13432])).
% 12.49/5.25  tff(c_7836, plain, (![A_1680, B_1681, C_1682]: (r2_hidden('#skF_2'(A_1680, B_1681, C_1682), k1_relat_1(B_1681)) | k7_relat_1(C_1682, A_1680)=B_1681 | k3_xboole_0(k1_relat_1(C_1682), A_1680)!=k1_relat_1(B_1681) | ~v1_funct_1(C_1682) | ~v1_relat_1(C_1682) | ~v1_funct_1(B_1681) | ~v1_relat_1(B_1681))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.49/5.25  tff(c_7845, plain, (![A_1680, C_1682]: (r2_hidden('#skF_2'(A_1680, k1_xboole_0, C_1682), k1_xboole_0) | k7_relat_1(C_1682, A_1680)=k1_xboole_0 | k3_xboole_0(k1_relat_1(C_1682), A_1680)!=k1_relat_1(k1_xboole_0) | ~v1_funct_1(C_1682) | ~v1_relat_1(C_1682) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_7836])).
% 12.49/5.25  tff(c_7851, plain, (![A_1680, C_1682]: (r2_hidden('#skF_2'(A_1680, k1_xboole_0, C_1682), k1_xboole_0) | k7_relat_1(C_1682, A_1680)=k1_xboole_0 | k3_xboole_0(k1_relat_1(C_1682), A_1680)!=k1_xboole_0 | ~v1_funct_1(C_1682) | ~v1_relat_1(C_1682))), inference(demodulation, [status(thm), theory('equality')], [c_1499, c_7302, c_24, c_7845])).
% 12.49/5.25  tff(c_7853, plain, (![C_1683, A_1684]: (k7_relat_1(C_1683, A_1684)=k1_xboole_0 | k3_xboole_0(k1_relat_1(C_1683), A_1684)!=k1_xboole_0 | ~v1_funct_1(C_1683) | ~v1_relat_1(C_1683))), inference(negUnitSimplification, [status(thm)], [c_7186, c_7851])).
% 12.49/5.25  tff(c_7874, plain, (![C_1685]: (k7_relat_1(C_1685, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_1685) | ~v1_relat_1(C_1685))), inference(superposition, [status(thm), theory('equality')], [c_10, c_7853])).
% 12.49/5.25  tff(c_7880, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_1498, c_7874])).
% 12.49/5.25  tff(c_7889, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_7880])).
% 12.49/5.25  tff(c_7334, plain, (![A_1604, B_1605]: (r1_xboole_0(A_1604, B_1605) | ~r1_subset_1(A_1604, B_1605) | v1_xboole_0(B_1605) | v1_xboole_0(A_1604))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.49/5.25  tff(c_7775, plain, (![A_1673, B_1674]: (k3_xboole_0(A_1673, B_1674)=k1_xboole_0 | ~r1_subset_1(A_1673, B_1674) | v1_xboole_0(B_1674) | v1_xboole_0(A_1673))), inference(resolution, [status(thm)], [c_7334, c_2])).
% 12.49/5.25  tff(c_7781, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_78, c_7775])).
% 12.49/5.25  tff(c_7785, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_82, c_7781])).
% 12.49/5.25  tff(c_7343, plain, (![A_1606, B_1607, C_1608]: (k9_subset_1(A_1606, B_1607, C_1608)=k3_xboole_0(B_1607, C_1608) | ~m1_subset_1(C_1608, k1_zfmisc_1(A_1606)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.49/5.25  tff(c_7356, plain, (![B_1607]: (k9_subset_1('#skF_3', B_1607, '#skF_6')=k3_xboole_0(B_1607, '#skF_6'))), inference(resolution, [status(thm)], [c_80, c_7343])).
% 12.49/5.25  tff(c_7661, plain, (![A_1650, B_1651, C_1652, D_1653]: (k2_partfun1(A_1650, B_1651, C_1652, D_1653)=k7_relat_1(C_1652, D_1653) | ~m1_subset_1(C_1652, k1_zfmisc_1(k2_zfmisc_1(A_1650, B_1651))) | ~v1_funct_1(C_1652))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.49/5.25  tff(c_7663, plain, (![D_1653]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_1653)=k7_relat_1('#skF_7', D_1653) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_72, c_7661])).
% 12.49/5.25  tff(c_7671, plain, (![D_1653]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_1653)=k7_relat_1('#skF_7', D_1653))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_7663])).
% 12.49/5.25  tff(c_7665, plain, (![D_1653]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_1653)=k7_relat_1('#skF_8', D_1653) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_66, c_7661])).
% 12.49/5.25  tff(c_7674, plain, (![D_1653]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_1653)=k7_relat_1('#skF_8', D_1653))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_7665])).
% 12.49/5.25  tff(c_7367, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k3_xboole_0('#skF_5', '#skF_6'))=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7356, c_7356, c_1475])).
% 12.49/5.25  tff(c_7831, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k7_relat_1('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7785, c_7785, c_7671, c_7674, c_7367])).
% 12.49/5.25  tff(c_7897, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7889, c_7831])).
% 12.49/5.25  tff(c_8018, plain, (![A_1697, E_1699, B_1700, C_1695, D_1696, F_1698]: (v1_funct_1(k1_tmap_1(A_1697, B_1700, C_1695, D_1696, E_1699, F_1698)) | ~m1_subset_1(F_1698, k1_zfmisc_1(k2_zfmisc_1(D_1696, B_1700))) | ~v1_funct_2(F_1698, D_1696, B_1700) | ~v1_funct_1(F_1698) | ~m1_subset_1(E_1699, k1_zfmisc_1(k2_zfmisc_1(C_1695, B_1700))) | ~v1_funct_2(E_1699, C_1695, B_1700) | ~v1_funct_1(E_1699) | ~m1_subset_1(D_1696, k1_zfmisc_1(A_1697)) | v1_xboole_0(D_1696) | ~m1_subset_1(C_1695, k1_zfmisc_1(A_1697)) | v1_xboole_0(C_1695) | v1_xboole_0(B_1700) | v1_xboole_0(A_1697))), inference(cnfTransformation, [status(thm)], [f_226])).
% 12.49/5.25  tff(c_8022, plain, (![A_1697, C_1695, E_1699]: (v1_funct_1(k1_tmap_1(A_1697, '#skF_4', C_1695, '#skF_6', E_1699, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_1699, k1_zfmisc_1(k2_zfmisc_1(C_1695, '#skF_4'))) | ~v1_funct_2(E_1699, C_1695, '#skF_4') | ~v1_funct_1(E_1699) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1697)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1695, k1_zfmisc_1(A_1697)) | v1_xboole_0(C_1695) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1697))), inference(resolution, [status(thm)], [c_66, c_8018])).
% 12.49/5.25  tff(c_8032, plain, (![A_1697, C_1695, E_1699]: (v1_funct_1(k1_tmap_1(A_1697, '#skF_4', C_1695, '#skF_6', E_1699, '#skF_8')) | ~m1_subset_1(E_1699, k1_zfmisc_1(k2_zfmisc_1(C_1695, '#skF_4'))) | ~v1_funct_2(E_1699, C_1695, '#skF_4') | ~v1_funct_1(E_1699) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1697)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1695, k1_zfmisc_1(A_1697)) | v1_xboole_0(C_1695) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1697))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_8022])).
% 12.49/5.25  tff(c_8061, plain, (![A_1702, C_1703, E_1704]: (v1_funct_1(k1_tmap_1(A_1702, '#skF_4', C_1703, '#skF_6', E_1704, '#skF_8')) | ~m1_subset_1(E_1704, k1_zfmisc_1(k2_zfmisc_1(C_1703, '#skF_4'))) | ~v1_funct_2(E_1704, C_1703, '#skF_4') | ~v1_funct_1(E_1704) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1702)) | ~m1_subset_1(C_1703, k1_zfmisc_1(A_1702)) | v1_xboole_0(C_1703) | v1_xboole_0(A_1702))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_8032])).
% 12.49/5.25  tff(c_8063, plain, (![A_1702]: (v1_funct_1(k1_tmap_1(A_1702, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1702)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1702)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1702))), inference(resolution, [status(thm)], [c_72, c_8061])).
% 12.49/5.25  tff(c_8071, plain, (![A_1702]: (v1_funct_1(k1_tmap_1(A_1702, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1702)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1702)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1702))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_8063])).
% 12.49/5.25  tff(c_8125, plain, (![A_1715]: (v1_funct_1(k1_tmap_1(A_1715, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1715)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1715)) | v1_xboole_0(A_1715))), inference(negUnitSimplification, [status(thm)], [c_86, c_8071])).
% 12.49/5.25  tff(c_8128, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_84, c_8125])).
% 12.49/5.25  tff(c_8131, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_8128])).
% 12.49/5.25  tff(c_8132, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_90, c_8131])).
% 12.49/5.25  tff(c_8335, plain, (![A_1755, E_1754, B_1759, F_1758, D_1757, C_1756]: (k2_partfun1(k4_subset_1(A_1755, C_1756, D_1757), B_1759, k1_tmap_1(A_1755, B_1759, C_1756, D_1757, E_1754, F_1758), D_1757)=F_1758 | ~m1_subset_1(k1_tmap_1(A_1755, B_1759, C_1756, D_1757, E_1754, F_1758), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1755, C_1756, D_1757), B_1759))) | ~v1_funct_2(k1_tmap_1(A_1755, B_1759, C_1756, D_1757, E_1754, F_1758), k4_subset_1(A_1755, C_1756, D_1757), B_1759) | ~v1_funct_1(k1_tmap_1(A_1755, B_1759, C_1756, D_1757, E_1754, F_1758)) | k2_partfun1(D_1757, B_1759, F_1758, k9_subset_1(A_1755, C_1756, D_1757))!=k2_partfun1(C_1756, B_1759, E_1754, k9_subset_1(A_1755, C_1756, D_1757)) | ~m1_subset_1(F_1758, k1_zfmisc_1(k2_zfmisc_1(D_1757, B_1759))) | ~v1_funct_2(F_1758, D_1757, B_1759) | ~v1_funct_1(F_1758) | ~m1_subset_1(E_1754, k1_zfmisc_1(k2_zfmisc_1(C_1756, B_1759))) | ~v1_funct_2(E_1754, C_1756, B_1759) | ~v1_funct_1(E_1754) | ~m1_subset_1(D_1757, k1_zfmisc_1(A_1755)) | v1_xboole_0(D_1757) | ~m1_subset_1(C_1756, k1_zfmisc_1(A_1755)) | v1_xboole_0(C_1756) | v1_xboole_0(B_1759) | v1_xboole_0(A_1755))), inference(cnfTransformation, [status(thm)], [f_192])).
% 12.49/5.25  tff(c_9201, plain, (![D_1935, B_1939, F_1937, A_1936, E_1938, C_1934]: (k2_partfun1(k4_subset_1(A_1936, C_1934, D_1935), B_1939, k1_tmap_1(A_1936, B_1939, C_1934, D_1935, E_1938, F_1937), D_1935)=F_1937 | ~v1_funct_2(k1_tmap_1(A_1936, B_1939, C_1934, D_1935, E_1938, F_1937), k4_subset_1(A_1936, C_1934, D_1935), B_1939) | ~v1_funct_1(k1_tmap_1(A_1936, B_1939, C_1934, D_1935, E_1938, F_1937)) | k2_partfun1(D_1935, B_1939, F_1937, k9_subset_1(A_1936, C_1934, D_1935))!=k2_partfun1(C_1934, B_1939, E_1938, k9_subset_1(A_1936, C_1934, D_1935)) | ~m1_subset_1(F_1937, k1_zfmisc_1(k2_zfmisc_1(D_1935, B_1939))) | ~v1_funct_2(F_1937, D_1935, B_1939) | ~v1_funct_1(F_1937) | ~m1_subset_1(E_1938, k1_zfmisc_1(k2_zfmisc_1(C_1934, B_1939))) | ~v1_funct_2(E_1938, C_1934, B_1939) | ~v1_funct_1(E_1938) | ~m1_subset_1(D_1935, k1_zfmisc_1(A_1936)) | v1_xboole_0(D_1935) | ~m1_subset_1(C_1934, k1_zfmisc_1(A_1936)) | v1_xboole_0(C_1934) | v1_xboole_0(B_1939) | v1_xboole_0(A_1936))), inference(resolution, [status(thm)], [c_58, c_8335])).
% 12.49/5.25  tff(c_9600, plain, (![C_2028, E_2032, D_2029, B_2033, F_2031, A_2030]: (k2_partfun1(k4_subset_1(A_2030, C_2028, D_2029), B_2033, k1_tmap_1(A_2030, B_2033, C_2028, D_2029, E_2032, F_2031), D_2029)=F_2031 | ~v1_funct_1(k1_tmap_1(A_2030, B_2033, C_2028, D_2029, E_2032, F_2031)) | k2_partfun1(D_2029, B_2033, F_2031, k9_subset_1(A_2030, C_2028, D_2029))!=k2_partfun1(C_2028, B_2033, E_2032, k9_subset_1(A_2030, C_2028, D_2029)) | ~m1_subset_1(F_2031, k1_zfmisc_1(k2_zfmisc_1(D_2029, B_2033))) | ~v1_funct_2(F_2031, D_2029, B_2033) | ~v1_funct_1(F_2031) | ~m1_subset_1(E_2032, k1_zfmisc_1(k2_zfmisc_1(C_2028, B_2033))) | ~v1_funct_2(E_2032, C_2028, B_2033) | ~v1_funct_1(E_2032) | ~m1_subset_1(D_2029, k1_zfmisc_1(A_2030)) | v1_xboole_0(D_2029) | ~m1_subset_1(C_2028, k1_zfmisc_1(A_2030)) | v1_xboole_0(C_2028) | v1_xboole_0(B_2033) | v1_xboole_0(A_2030))), inference(resolution, [status(thm)], [c_60, c_9201])).
% 12.49/5.25  tff(c_9606, plain, (![A_2030, C_2028, E_2032]: (k2_partfun1(k4_subset_1(A_2030, C_2028, '#skF_6'), '#skF_4', k1_tmap_1(A_2030, '#skF_4', C_2028, '#skF_6', E_2032, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_2030, '#skF_4', C_2028, '#skF_6', E_2032, '#skF_8')) | k2_partfun1(C_2028, '#skF_4', E_2032, k9_subset_1(A_2030, C_2028, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_2030, C_2028, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_2032, k1_zfmisc_1(k2_zfmisc_1(C_2028, '#skF_4'))) | ~v1_funct_2(E_2032, C_2028, '#skF_4') | ~v1_funct_1(E_2032) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2030)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_2028, k1_zfmisc_1(A_2030)) | v1_xboole_0(C_2028) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2030))), inference(resolution, [status(thm)], [c_66, c_9600])).
% 12.49/5.25  tff(c_9617, plain, (![A_2030, C_2028, E_2032]: (k2_partfun1(k4_subset_1(A_2030, C_2028, '#skF_6'), '#skF_4', k1_tmap_1(A_2030, '#skF_4', C_2028, '#skF_6', E_2032, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_2030, '#skF_4', C_2028, '#skF_6', E_2032, '#skF_8')) | k2_partfun1(C_2028, '#skF_4', E_2032, k9_subset_1(A_2030, C_2028, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2030, C_2028, '#skF_6')) | ~m1_subset_1(E_2032, k1_zfmisc_1(k2_zfmisc_1(C_2028, '#skF_4'))) | ~v1_funct_2(E_2032, C_2028, '#skF_4') | ~v1_funct_1(E_2032) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2030)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_2028, k1_zfmisc_1(A_2030)) | v1_xboole_0(C_2028) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2030))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_7674, c_9606])).
% 12.49/5.25  tff(c_10304, plain, (![A_2115, C_2116, E_2117]: (k2_partfun1(k4_subset_1(A_2115, C_2116, '#skF_6'), '#skF_4', k1_tmap_1(A_2115, '#skF_4', C_2116, '#skF_6', E_2117, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_2115, '#skF_4', C_2116, '#skF_6', E_2117, '#skF_8')) | k2_partfun1(C_2116, '#skF_4', E_2117, k9_subset_1(A_2115, C_2116, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2115, C_2116, '#skF_6')) | ~m1_subset_1(E_2117, k1_zfmisc_1(k2_zfmisc_1(C_2116, '#skF_4'))) | ~v1_funct_2(E_2117, C_2116, '#skF_4') | ~v1_funct_1(E_2117) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2115)) | ~m1_subset_1(C_2116, k1_zfmisc_1(A_2115)) | v1_xboole_0(C_2116) | v1_xboole_0(A_2115))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_9617])).
% 12.49/5.25  tff(c_10309, plain, (![A_2115]: (k2_partfun1(k4_subset_1(A_2115, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_2115, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_2115, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_2115, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2115, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2115)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2115)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_2115))), inference(resolution, [status(thm)], [c_72, c_10304])).
% 12.49/5.25  tff(c_10320, plain, (![A_2115]: (k2_partfun1(k4_subset_1(A_2115, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_2115, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_2115, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_2115, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2115, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2115)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2115)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_2115))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_7671, c_10309])).
% 12.49/5.25  tff(c_10466, plain, (![A_2139]: (k2_partfun1(k4_subset_1(A_2139, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_2139, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_2139, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_2139, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2139, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2139)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2139)) | v1_xboole_0(A_2139))), inference(negUnitSimplification, [status(thm)], [c_86, c_10320])).
% 12.49/5.25  tff(c_1474, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_64])).
% 12.49/5.25  tff(c_7303, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitLeft, [status(thm)], [c_1474])).
% 12.49/5.25  tff(c_10477, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10466, c_7303])).
% 12.49/5.25  tff(c_10491, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_7889, c_7785, c_7356, c_7897, c_7785, c_7356, c_8132, c_10477])).
% 12.49/5.25  tff(c_10493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_10491])).
% 12.49/5.25  tff(c_10494, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_1474])).
% 12.49/5.25  tff(c_13474, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13465, c_10494])).
% 12.49/5.25  tff(c_13485, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_11137, c_11033, c_10548, c_11145, c_11033, c_10548, c_11380, c_13474])).
% 12.49/5.25  tff(c_13487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_13485])).
% 12.49/5.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.49/5.25  
% 12.49/5.25  Inference rules
% 12.49/5.25  ----------------------
% 12.49/5.25  #Ref     : 8
% 12.49/5.25  #Sup     : 2840
% 12.49/5.25  #Fact    : 0
% 12.49/5.25  #Define  : 0
% 12.49/5.25  #Split   : 127
% 12.49/5.25  #Chain   : 0
% 12.49/5.25  #Close   : 0
% 12.49/5.25  
% 12.49/5.25  Ordering : KBO
% 12.49/5.25  
% 12.49/5.25  Simplification rules
% 12.49/5.25  ----------------------
% 12.49/5.25  #Subsume      : 405
% 12.49/5.25  #Demod        : 2176
% 12.49/5.25  #Tautology    : 1049
% 12.49/5.25  #SimpNegUnit  : 400
% 12.49/5.25  #BackRed      : 43
% 12.49/5.25  
% 12.49/5.25  #Partial instantiations: 0
% 12.49/5.25  #Strategies tried      : 1
% 12.49/5.25  
% 12.49/5.25  Timing (in seconds)
% 12.49/5.25  ----------------------
% 12.49/5.25  Preprocessing        : 0.44
% 12.49/5.25  Parsing              : 0.21
% 12.49/5.25  CNF conversion       : 0.06
% 12.49/5.25  Main loop            : 4.02
% 12.49/5.25  Inferencing          : 1.44
% 12.49/5.25  Reduction            : 1.37
% 12.49/5.25  Demodulation         : 0.99
% 12.49/5.25  BG Simplification    : 0.11
% 12.49/5.25  Subsumption          : 0.85
% 12.49/5.25  Abstraction          : 0.14
% 12.49/5.25  MUC search           : 0.00
% 12.49/5.25  Cooper               : 0.00
% 12.49/5.25  Total                : 4.52
% 12.49/5.25  Index Insertion      : 0.00
% 12.49/5.25  Index Deletion       : 0.00
% 12.49/5.25  Index Matching       : 0.00
% 12.49/5.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
