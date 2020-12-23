%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:15 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 326 expanded)
%              Number of leaves         :   45 ( 138 expanded)
%              Depth                    :   10
%              Number of atoms          :  206 (1006 expanded)
%              Number of equality atoms :   37 ( 107 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_170,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_89,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_111,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_109,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_68,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_150,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_40,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_52,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_124,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_34,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_1'(A_21),A_21)
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_44,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_16,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_68,plain,(
    ! [A_6] : v2_funct_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_16])).

tff(c_542,plain,(
    ! [F_153,C_151,B_148,D_150,E_152,A_149] :
      ( m1_subset_1(k1_partfun1(A_149,B_148,C_151,D_150,E_152,F_153),k1_zfmisc_1(k2_zfmisc_1(A_149,D_150)))
      | ~ m1_subset_1(F_153,k1_zfmisc_1(k2_zfmisc_1(C_151,D_150)))
      | ~ v1_funct_1(F_153)
      | ~ m1_subset_1(E_152,k1_zfmisc_1(k2_zfmisc_1(A_149,B_148)))
      | ~ v1_funct_1(E_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30,plain,(
    ! [A_20] : m1_subset_1(k6_relat_1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_67,plain,(
    ! [A_20] : m1_subset_1(k6_partfun1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_30])).

tff(c_54,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_358,plain,(
    ! [D_107,C_108,A_109,B_110] :
      ( D_107 = C_108
      | ~ r2_relset_1(A_109,B_110,C_108,D_107)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_368,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_358])).

tff(c_387,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_368])).

tff(c_448,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_387])).

tff(c_548,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_542,c_448])).

tff(c_577,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_548])).

tff(c_578,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_387])).

tff(c_917,plain,(
    ! [A_233,D_234,C_235,E_232,B_231] :
      ( k1_xboole_0 = C_235
      | v2_funct_1(D_234)
      | ~ v2_funct_1(k1_partfun1(A_233,B_231,B_231,C_235,D_234,E_232))
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1(B_231,C_235)))
      | ~ v1_funct_2(E_232,B_231,C_235)
      | ~ v1_funct_1(E_232)
      | ~ m1_subset_1(D_234,k1_zfmisc_1(k2_zfmisc_1(A_233,B_231)))
      | ~ v1_funct_2(D_234,A_233,B_231)
      | ~ v1_funct_1(D_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_919,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_917])).

tff(c_921,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_56,c_68,c_919])).

tff(c_922,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_921])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_959,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_922,c_2])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_956,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_922,c_922,c_8])).

tff(c_201,plain,(
    ! [C_81,B_82,A_83] :
      ( ~ v1_xboole_0(C_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(C_81))
      | ~ r2_hidden(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_214,plain,(
    ! [A_83] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_83,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_201])).

tff(c_223,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_1065,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_223])).

tff(c_1069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_1065])).

tff(c_1072,plain,(
    ! [A_251] : ~ r2_hidden(A_251,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_1077,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_1072])).

tff(c_100,plain,(
    ! [A_68] : k6_relat_1(A_68) = k6_partfun1(A_68) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_106,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_12])).

tff(c_119,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_68])).

tff(c_1103,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_119])).

tff(c_1111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_1103])).

tff(c_1112,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1143,plain,(
    ! [C_259,A_260,B_261] :
      ( v1_relat_1(C_259)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1159,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_1143])).

tff(c_1189,plain,(
    ! [C_267,B_268,A_269] :
      ( v5_relat_1(C_267,B_268)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_269,B_268))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1206,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1189])).

tff(c_1257,plain,(
    ! [A_282,B_283,D_284] :
      ( r2_relset_1(A_282,B_283,D_284,D_284)
      | ~ m1_subset_1(D_284,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1268,plain,(
    ! [A_20] : r2_relset_1(A_20,A_20,k6_partfun1(A_20),k6_partfun1(A_20)) ),
    inference(resolution,[status(thm)],[c_67,c_1257])).

tff(c_1313,plain,(
    ! [A_289,B_290,C_291] :
      ( k2_relset_1(A_289,B_290,C_291) = k2_relat_1(C_291)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1330,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_1313])).

tff(c_1518,plain,(
    ! [F_337,E_336,A_333,B_332,C_335,D_334] :
      ( m1_subset_1(k1_partfun1(A_333,B_332,C_335,D_334,E_336,F_337),k1_zfmisc_1(k2_zfmisc_1(A_333,D_334)))
      | ~ m1_subset_1(F_337,k1_zfmisc_1(k2_zfmisc_1(C_335,D_334)))
      | ~ v1_funct_1(F_337)
      | ~ m1_subset_1(E_336,k1_zfmisc_1(k2_zfmisc_1(A_333,B_332)))
      | ~ v1_funct_1(E_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1340,plain,(
    ! [D_292,C_293,A_294,B_295] :
      ( D_292 = C_293
      | ~ r2_relset_1(A_294,B_295,C_293,D_292)
      | ~ m1_subset_1(D_292,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295)))
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1350,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_1340])).

tff(c_1369,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_1350])).

tff(c_1424,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1369])).

tff(c_1524,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1518,c_1424])).

tff(c_1553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_1524])).

tff(c_1554,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1369])).

tff(c_1904,plain,(
    ! [A_436,B_437,C_438,D_439] :
      ( k2_relset_1(A_436,B_437,C_438) = B_437
      | ~ r2_relset_1(B_437,B_437,k1_partfun1(B_437,A_436,A_436,B_437,D_439,C_438),k6_partfun1(B_437))
      | ~ m1_subset_1(D_439,k1_zfmisc_1(k2_zfmisc_1(B_437,A_436)))
      | ~ v1_funct_2(D_439,B_437,A_436)
      | ~ v1_funct_1(D_439)
      | ~ m1_subset_1(C_438,k1_zfmisc_1(k2_zfmisc_1(A_436,B_437)))
      | ~ v1_funct_2(C_438,A_436,B_437)
      | ~ v1_funct_1(C_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1907,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1554,c_1904])).

tff(c_1912,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_66,c_64,c_62,c_1268,c_1330,c_1907])).

tff(c_36,plain,(
    ! [B_44] :
      ( v2_funct_2(B_44,k2_relat_1(B_44))
      | ~ v5_relat_1(B_44,k2_relat_1(B_44))
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1918,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1912,c_36])).

tff(c_1922,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1159,c_1206,c_1912,c_1918])).

tff(c_1924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1112,c_1922])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:41:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.86  
% 4.63/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.86  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.63/1.86  
% 4.63/1.86  %Foreground sorts:
% 4.63/1.86  
% 4.63/1.86  
% 4.63/1.86  %Background operators:
% 4.63/1.86  
% 4.63/1.86  
% 4.63/1.86  %Foreground operators:
% 4.63/1.86  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.63/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.63/1.86  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.63/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.86  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.63/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.63/1.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.63/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.63/1.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.63/1.86  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.63/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.63/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.63/1.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.63/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.63/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.63/1.86  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.63/1.86  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.63/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.63/1.86  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.63/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.63/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.63/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.63/1.86  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.63/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.86  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.63/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.63/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.63/1.86  
% 4.63/1.88  tff(f_170, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 4.63/1.88  tff(f_89, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 4.63/1.88  tff(f_111, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.63/1.88  tff(f_44, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.63/1.88  tff(f_109, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.63/1.88  tff(f_68, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.63/1.88  tff(f_66, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.63/1.88  tff(f_150, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 4.63/1.88  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.63/1.88  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.63/1.88  tff(f_39, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.63/1.88  tff(f_40, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 4.63/1.88  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.63/1.88  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.63/1.88  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.63/1.88  tff(f_128, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.63/1.88  tff(f_97, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.63/1.88  tff(c_52, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.63/1.88  tff(c_124, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 4.63/1.88  tff(c_34, plain, (![A_21]: (r2_hidden('#skF_1'(A_21), A_21) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.63/1.88  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.63/1.88  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.63/1.88  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.63/1.88  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.63/1.88  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.63/1.88  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.63/1.88  tff(c_44, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.63/1.88  tff(c_16, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.63/1.88  tff(c_68, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_16])).
% 4.63/1.88  tff(c_542, plain, (![F_153, C_151, B_148, D_150, E_152, A_149]: (m1_subset_1(k1_partfun1(A_149, B_148, C_151, D_150, E_152, F_153), k1_zfmisc_1(k2_zfmisc_1(A_149, D_150))) | ~m1_subset_1(F_153, k1_zfmisc_1(k2_zfmisc_1(C_151, D_150))) | ~v1_funct_1(F_153) | ~m1_subset_1(E_152, k1_zfmisc_1(k2_zfmisc_1(A_149, B_148))) | ~v1_funct_1(E_152))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.63/1.88  tff(c_30, plain, (![A_20]: (m1_subset_1(k6_relat_1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.63/1.88  tff(c_67, plain, (![A_20]: (m1_subset_1(k6_partfun1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_30])).
% 4.63/1.88  tff(c_54, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.63/1.88  tff(c_358, plain, (![D_107, C_108, A_109, B_110]: (D_107=C_108 | ~r2_relset_1(A_109, B_110, C_108, D_107) | ~m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.63/1.88  tff(c_368, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_358])).
% 4.63/1.88  tff(c_387, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_368])).
% 4.63/1.88  tff(c_448, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_387])).
% 4.63/1.88  tff(c_548, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_542, c_448])).
% 4.63/1.88  tff(c_577, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_548])).
% 4.63/1.88  tff(c_578, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_387])).
% 4.63/1.88  tff(c_917, plain, (![A_233, D_234, C_235, E_232, B_231]: (k1_xboole_0=C_235 | v2_funct_1(D_234) | ~v2_funct_1(k1_partfun1(A_233, B_231, B_231, C_235, D_234, E_232)) | ~m1_subset_1(E_232, k1_zfmisc_1(k2_zfmisc_1(B_231, C_235))) | ~v1_funct_2(E_232, B_231, C_235) | ~v1_funct_1(E_232) | ~m1_subset_1(D_234, k1_zfmisc_1(k2_zfmisc_1(A_233, B_231))) | ~v1_funct_2(D_234, A_233, B_231) | ~v1_funct_1(D_234))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.63/1.88  tff(c_919, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_578, c_917])).
% 4.63/1.88  tff(c_921, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_56, c_68, c_919])).
% 4.63/1.88  tff(c_922, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_124, c_921])).
% 4.63/1.88  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.63/1.88  tff(c_959, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_922, c_2])).
% 4.63/1.88  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.63/1.88  tff(c_956, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_922, c_922, c_8])).
% 4.63/1.88  tff(c_201, plain, (![C_81, B_82, A_83]: (~v1_xboole_0(C_81) | ~m1_subset_1(B_82, k1_zfmisc_1(C_81)) | ~r2_hidden(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.63/1.88  tff(c_214, plain, (![A_83]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_83, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_201])).
% 4.63/1.88  tff(c_223, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_214])).
% 4.63/1.88  tff(c_1065, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_956, c_223])).
% 4.63/1.88  tff(c_1069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_959, c_1065])).
% 4.63/1.88  tff(c_1072, plain, (![A_251]: (~r2_hidden(A_251, '#skF_4'))), inference(splitRight, [status(thm)], [c_214])).
% 4.63/1.88  tff(c_1077, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_1072])).
% 4.63/1.88  tff(c_100, plain, (![A_68]: (k6_relat_1(A_68)=k6_partfun1(A_68))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.63/1.88  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.63/1.88  tff(c_106, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_100, c_12])).
% 4.63/1.88  tff(c_119, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_106, c_68])).
% 4.63/1.88  tff(c_1103, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_119])).
% 4.63/1.88  tff(c_1111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_1103])).
% 4.63/1.88  tff(c_1112, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 4.63/1.88  tff(c_1143, plain, (![C_259, A_260, B_261]: (v1_relat_1(C_259) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.63/1.88  tff(c_1159, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_1143])).
% 4.63/1.88  tff(c_1189, plain, (![C_267, B_268, A_269]: (v5_relat_1(C_267, B_268) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_269, B_268))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.63/1.88  tff(c_1206, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_1189])).
% 4.63/1.88  tff(c_1257, plain, (![A_282, B_283, D_284]: (r2_relset_1(A_282, B_283, D_284, D_284) | ~m1_subset_1(D_284, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.63/1.88  tff(c_1268, plain, (![A_20]: (r2_relset_1(A_20, A_20, k6_partfun1(A_20), k6_partfun1(A_20)))), inference(resolution, [status(thm)], [c_67, c_1257])).
% 4.63/1.88  tff(c_1313, plain, (![A_289, B_290, C_291]: (k2_relset_1(A_289, B_290, C_291)=k2_relat_1(C_291) | ~m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.63/1.88  tff(c_1330, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_1313])).
% 4.63/1.88  tff(c_1518, plain, (![F_337, E_336, A_333, B_332, C_335, D_334]: (m1_subset_1(k1_partfun1(A_333, B_332, C_335, D_334, E_336, F_337), k1_zfmisc_1(k2_zfmisc_1(A_333, D_334))) | ~m1_subset_1(F_337, k1_zfmisc_1(k2_zfmisc_1(C_335, D_334))) | ~v1_funct_1(F_337) | ~m1_subset_1(E_336, k1_zfmisc_1(k2_zfmisc_1(A_333, B_332))) | ~v1_funct_1(E_336))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.63/1.88  tff(c_1340, plain, (![D_292, C_293, A_294, B_295]: (D_292=C_293 | ~r2_relset_1(A_294, B_295, C_293, D_292) | ~m1_subset_1(D_292, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.63/1.88  tff(c_1350, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_1340])).
% 4.63/1.88  tff(c_1369, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_1350])).
% 4.63/1.88  tff(c_1424, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1369])).
% 4.63/1.88  tff(c_1524, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1518, c_1424])).
% 4.63/1.88  tff(c_1553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_1524])).
% 4.63/1.88  tff(c_1554, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1369])).
% 4.63/1.88  tff(c_1904, plain, (![A_436, B_437, C_438, D_439]: (k2_relset_1(A_436, B_437, C_438)=B_437 | ~r2_relset_1(B_437, B_437, k1_partfun1(B_437, A_436, A_436, B_437, D_439, C_438), k6_partfun1(B_437)) | ~m1_subset_1(D_439, k1_zfmisc_1(k2_zfmisc_1(B_437, A_436))) | ~v1_funct_2(D_439, B_437, A_436) | ~v1_funct_1(D_439) | ~m1_subset_1(C_438, k1_zfmisc_1(k2_zfmisc_1(A_436, B_437))) | ~v1_funct_2(C_438, A_436, B_437) | ~v1_funct_1(C_438))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.63/1.88  tff(c_1907, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1554, c_1904])).
% 4.63/1.88  tff(c_1912, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_66, c_64, c_62, c_1268, c_1330, c_1907])).
% 4.63/1.88  tff(c_36, plain, (![B_44]: (v2_funct_2(B_44, k2_relat_1(B_44)) | ~v5_relat_1(B_44, k2_relat_1(B_44)) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.63/1.88  tff(c_1918, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1912, c_36])).
% 4.63/1.88  tff(c_1922, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1159, c_1206, c_1912, c_1918])).
% 4.63/1.88  tff(c_1924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1112, c_1922])).
% 4.63/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.88  
% 4.63/1.88  Inference rules
% 4.63/1.88  ----------------------
% 4.63/1.88  #Ref     : 0
% 4.63/1.88  #Sup     : 418
% 4.63/1.88  #Fact    : 0
% 4.63/1.88  #Define  : 0
% 4.63/1.88  #Split   : 14
% 4.63/1.88  #Chain   : 0
% 4.63/1.88  #Close   : 0
% 4.63/1.88  
% 4.63/1.88  Ordering : KBO
% 4.63/1.88  
% 4.63/1.88  Simplification rules
% 4.63/1.88  ----------------------
% 4.63/1.88  #Subsume      : 41
% 4.63/1.88  #Demod        : 393
% 4.63/1.88  #Tautology    : 128
% 4.63/1.88  #SimpNegUnit  : 5
% 4.63/1.88  #BackRed      : 94
% 4.63/1.88  
% 4.63/1.88  #Partial instantiations: 0
% 4.63/1.88  #Strategies tried      : 1
% 4.63/1.88  
% 4.63/1.88  Timing (in seconds)
% 4.63/1.88  ----------------------
% 4.63/1.88  Preprocessing        : 0.36
% 4.63/1.88  Parsing              : 0.19
% 4.63/1.88  CNF conversion       : 0.03
% 4.63/1.88  Main loop            : 0.69
% 4.63/1.88  Inferencing          : 0.24
% 4.63/1.88  Reduction            : 0.25
% 4.63/1.88  Demodulation         : 0.17
% 4.63/1.88  BG Simplification    : 0.03
% 4.63/1.88  Subsumption          : 0.11
% 4.63/1.88  Abstraction          : 0.03
% 4.63/1.88  MUC search           : 0.00
% 4.63/1.88  Cooper               : 0.00
% 4.63/1.88  Total                : 1.09
% 4.63/1.88  Index Insertion      : 0.00
% 4.63/1.88  Index Deletion       : 0.00
% 4.63/1.88  Index Matching       : 0.00
% 4.63/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
