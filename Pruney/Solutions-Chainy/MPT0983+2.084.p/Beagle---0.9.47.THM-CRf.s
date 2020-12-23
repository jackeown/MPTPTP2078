%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:13 EST 2020

% Result     : Theorem 6.27s
% Output     : CNFRefutation 6.51s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 421 expanded)
%              Number of leaves         :   45 ( 164 expanded)
%              Depth                    :   13
%              Number of atoms          :  251 (1214 expanded)
%              Number of equality atoms :   41 (  99 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(f_162,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_103,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_57,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_81,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_142,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_120,axiom,(
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

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_48,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_76,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( v1_xboole_0(k2_zfmisc_1(A_9,B_10))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_222,plain,(
    ! [C_78,B_79,A_80] :
      ( ~ v1_xboole_0(C_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(C_78))
      | ~ r2_hidden(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_236,plain,(
    ! [A_80] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_80,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_222])).

tff(c_3841,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_3849,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_3841])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( v1_xboole_0(k2_zfmisc_1(A_7,B_8))
      | ~ v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_235,plain,(
    ! [A_80] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2'))
      | ~ r2_hidden(A_80,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_222])).

tff(c_275,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_289,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_275])).

tff(c_40,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_16,plain,(
    ! [A_14] : v2_funct_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,(
    ! [A_14] : v2_funct_1(k6_partfun1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16])).

tff(c_36,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] :
      ( m1_subset_1(k1_partfun1(A_31,B_32,C_33,D_34,E_35,F_36),k1_zfmisc_1(k2_zfmisc_1(A_31,D_34)))
      | ~ m1_subset_1(F_36,k1_zfmisc_1(k2_zfmisc_1(C_33,D_34)))
      | ~ v1_funct_1(F_36)
      | ~ m1_subset_1(E_35,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_1(E_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    ! [A_28] : m1_subset_1(k6_relat_1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_63,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30])).

tff(c_50,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_464,plain,(
    ! [D_108,C_109,A_110,B_111] :
      ( D_108 = C_109
      | ~ r2_relset_1(A_110,B_111,C_109,D_108)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_474,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_50,c_464])).

tff(c_493,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_474])).

tff(c_546,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_493])).

tff(c_2108,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_546])).

tff(c_2112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_52,c_2108])).

tff(c_2113,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_493])).

tff(c_46,plain,(
    ! [E_48,D_46,C_45,A_43,B_44] :
      ( k1_xboole_0 = C_45
      | v2_funct_1(D_46)
      | ~ v2_funct_1(k1_partfun1(A_43,B_44,B_44,C_45,D_46,E_48))
      | ~ m1_subset_1(E_48,k1_zfmisc_1(k2_zfmisc_1(B_44,C_45)))
      | ~ v1_funct_2(E_48,B_44,C_45)
      | ~ v1_funct_1(E_48)
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_funct_2(D_46,A_43,B_44)
      | ~ v1_funct_1(D_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_3679,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2113,c_46])).

tff(c_3686,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_52,c_64,c_3679])).

tff(c_3687,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3686])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3725,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3687,c_6])).

tff(c_3727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_3725])).

tff(c_3729,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_3730,plain,(
    ! [A_267] : ~ r2_hidden(A_267,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_3735,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_3730])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3903,plain,(
    ! [A_278] :
      ( A_278 = '#skF_5'
      | ~ v1_xboole_0(A_278) ) ),
    inference(resolution,[status(thm)],[c_3735,c_8])).

tff(c_3916,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3729,c_3903])).

tff(c_3922,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3916,c_52])).

tff(c_4036,plain,(
    ! [D_289,C_290,A_291,B_292] :
      ( D_289 = C_290
      | ~ r2_relset_1(A_291,B_292,C_290,D_289)
      | ~ m1_subset_1(D_289,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292)))
      | ~ m1_subset_1(C_290,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4042,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_50,c_4036])).

tff(c_4053,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_4042])).

tff(c_4056,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_4053])).

tff(c_4327,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_4056])).

tff(c_4331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_3922,c_3916,c_4327])).

tff(c_4332,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4053])).

tff(c_78,plain,(
    ! [B_56,A_57] :
      ( ~ v1_xboole_0(B_56)
      | B_56 = A_57
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_84,plain,(
    ! [A_57] :
      ( k1_xboole_0 = A_57
      | ~ v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_78])).

tff(c_3747,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3735,c_84])).

tff(c_4718,plain,(
    ! [A_375,E_372,D_374,C_373,B_376] :
      ( C_373 = '#skF_5'
      | v2_funct_1(D_374)
      | ~ v2_funct_1(k1_partfun1(A_375,B_376,B_376,C_373,D_374,E_372))
      | ~ m1_subset_1(E_372,k1_zfmisc_1(k2_zfmisc_1(B_376,C_373)))
      | ~ v1_funct_2(E_372,B_376,C_373)
      | ~ v1_funct_1(E_372)
      | ~ m1_subset_1(D_374,k1_zfmisc_1(k2_zfmisc_1(A_375,B_376)))
      | ~ v1_funct_2(D_374,A_375,B_376)
      | ~ v1_funct_1(D_374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3747,c_46])).

tff(c_4720,plain,
    ( '#skF_5' = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4332,c_4718])).

tff(c_4722,plain,
    ( '#skF_5' = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_3922,c_3916,c_64,c_4720])).

tff(c_4723,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4722])).

tff(c_4752,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4723,c_3735])).

tff(c_4758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3849,c_4752])).

tff(c_4761,plain,(
    ! [A_377] : ~ r2_hidden(A_377,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_4766,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_4761])).

tff(c_4773,plain,(
    ! [A_378] :
      ( A_378 = '#skF_5'
      | ~ v1_xboole_0(A_378) ) ),
    inference(resolution,[status(thm)],[c_3735,c_8])).

tff(c_4793,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4766,c_4773])).

tff(c_100,plain,(
    ! [A_60,B_61] :
      ( v1_xboole_0(k2_zfmisc_1(A_60,B_61))
      | ~ v1_xboole_0(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_134,plain,(
    ! [A_65,B_66] :
      ( k2_zfmisc_1(A_65,B_66) = k1_xboole_0
      | ~ v1_xboole_0(B_66) ) ),
    inference(resolution,[status(thm)],[c_100,c_84])).

tff(c_143,plain,(
    ! [A_65] : k2_zfmisc_1(A_65,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_168,plain,(
    ! [A_68] : m1_subset_1(k6_partfun1(A_68),k1_zfmisc_1(k2_zfmisc_1(A_68,A_68))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30])).

tff(c_172,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_168])).

tff(c_224,plain,(
    ! [A_80] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_80,k6_partfun1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_172,c_222])).

tff(c_237,plain,(
    ! [A_81] : ~ r2_hidden(A_81,k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_224])).

tff(c_242,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_237])).

tff(c_254,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_242,c_84])).

tff(c_270,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_64])).

tff(c_3768,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3747,c_270])).

tff(c_4805,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4793,c_3768])).

tff(c_4816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4805])).

tff(c_4817,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_4920,plain,(
    ! [C_394,A_395,B_396] :
      ( v1_relat_1(C_394)
      | ~ m1_subset_1(C_394,k1_zfmisc_1(k2_zfmisc_1(A_395,B_396))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4935,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_4920])).

tff(c_5053,plain,(
    ! [C_408,B_409,A_410] :
      ( v5_relat_1(C_408,B_409)
      | ~ m1_subset_1(C_408,k1_zfmisc_1(k2_zfmisc_1(A_410,B_409))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5070,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_5053])).

tff(c_5136,plain,(
    ! [A_420,B_421,C_422] :
      ( k2_relset_1(A_420,B_421,C_422) = k2_relat_1(C_422)
      | ~ m1_subset_1(C_422,k1_zfmisc_1(k2_zfmisc_1(A_420,B_421))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5153,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_5136])).

tff(c_6727,plain,(
    ! [A_512,B_513,C_514,D_515] :
      ( k2_relset_1(A_512,B_513,C_514) = B_513
      | ~ r2_relset_1(B_513,B_513,k1_partfun1(B_513,A_512,A_512,B_513,D_515,C_514),k6_partfun1(B_513))
      | ~ m1_subset_1(D_515,k1_zfmisc_1(k2_zfmisc_1(B_513,A_512)))
      | ~ v1_funct_2(D_515,B_513,A_512)
      | ~ v1_funct_1(D_515)
      | ~ m1_subset_1(C_514,k1_zfmisc_1(k2_zfmisc_1(A_512,B_513)))
      | ~ v1_funct_2(C_514,A_512,B_513)
      | ~ v1_funct_1(C_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_6745,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_6727])).

tff(c_6749,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_62,c_60,c_58,c_5153,c_6745])).

tff(c_32,plain,(
    ! [B_30] :
      ( v2_funct_2(B_30,k2_relat_1(B_30))
      | ~ v5_relat_1(B_30,k2_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6754,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6749,c_32])).

tff(c_6758,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4935,c_5070,c_6749,c_6754])).

tff(c_6760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4817,c_6758])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:33:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.27/2.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.51/2.30  
% 6.51/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.51/2.30  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 6.51/2.30  
% 6.51/2.30  %Foreground sorts:
% 6.51/2.30  
% 6.51/2.30  
% 6.51/2.30  %Background operators:
% 6.51/2.30  
% 6.51/2.30  
% 6.51/2.30  %Foreground operators:
% 6.51/2.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.51/2.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.51/2.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.51/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.51/2.30  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.51/2.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.51/2.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.51/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.51/2.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.51/2.30  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.51/2.30  tff('#skF_5', type, '#skF_5': $i).
% 6.51/2.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.51/2.30  tff('#skF_2', type, '#skF_2': $i).
% 6.51/2.30  tff('#skF_3', type, '#skF_3': $i).
% 6.51/2.30  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.51/2.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.51/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.51/2.30  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.51/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.51/2.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.51/2.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.51/2.30  tff('#skF_4', type, '#skF_4': $i).
% 6.51/2.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.51/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.51/2.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.51/2.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.51/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.51/2.30  
% 6.51/2.32  tff(f_162, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 6.51/2.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.51/2.32  tff(f_48, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 6.51/2.32  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 6.51/2.32  tff(f_44, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 6.51/2.32  tff(f_103, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.51/2.32  tff(f_57, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 6.51/2.32  tff(f_101, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.51/2.32  tff(f_81, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 6.51/2.32  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.51/2.32  tff(f_142, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 6.51/2.32  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.51/2.32  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 6.51/2.32  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.51/2.32  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.51/2.32  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.51/2.32  tff(f_120, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 6.51/2.32  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.51/2.32  tff(c_48, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.51/2.32  tff(c_76, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 6.51/2.32  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.51/2.32  tff(c_12, plain, (![A_9, B_10]: (v1_xboole_0(k2_zfmisc_1(A_9, B_10)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.51/2.32  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.51/2.32  tff(c_222, plain, (![C_78, B_79, A_80]: (~v1_xboole_0(C_78) | ~m1_subset_1(B_79, k1_zfmisc_1(C_78)) | ~r2_hidden(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.51/2.32  tff(c_236, plain, (![A_80]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_80, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_222])).
% 6.51/2.32  tff(c_3841, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_236])).
% 6.51/2.32  tff(c_3849, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_3841])).
% 6.51/2.32  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.51/2.32  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.51/2.32  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.51/2.32  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.51/2.32  tff(c_10, plain, (![A_7, B_8]: (v1_xboole_0(k2_zfmisc_1(A_7, B_8)) | ~v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.51/2.32  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.51/2.32  tff(c_235, plain, (![A_80]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2')) | ~r2_hidden(A_80, '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_222])).
% 6.51/2.32  tff(c_275, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_235])).
% 6.51/2.32  tff(c_289, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_10, c_275])).
% 6.51/2.32  tff(c_40, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.51/2.32  tff(c_16, plain, (![A_14]: (v2_funct_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.51/2.32  tff(c_64, plain, (![A_14]: (v2_funct_1(k6_partfun1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16])).
% 6.51/2.32  tff(c_36, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (m1_subset_1(k1_partfun1(A_31, B_32, C_33, D_34, E_35, F_36), k1_zfmisc_1(k2_zfmisc_1(A_31, D_34))) | ~m1_subset_1(F_36, k1_zfmisc_1(k2_zfmisc_1(C_33, D_34))) | ~v1_funct_1(F_36) | ~m1_subset_1(E_35, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_1(E_35))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.51/2.32  tff(c_30, plain, (![A_28]: (m1_subset_1(k6_relat_1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.51/2.32  tff(c_63, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30])).
% 6.51/2.32  tff(c_50, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.51/2.32  tff(c_464, plain, (![D_108, C_109, A_110, B_111]: (D_108=C_109 | ~r2_relset_1(A_110, B_111, C_109, D_108) | ~m1_subset_1(D_108, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.51/2.32  tff(c_474, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_50, c_464])).
% 6.51/2.32  tff(c_493, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_474])).
% 6.51/2.32  tff(c_546, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_493])).
% 6.51/2.32  tff(c_2108, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_546])).
% 6.51/2.32  tff(c_2112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_56, c_52, c_2108])).
% 6.51/2.32  tff(c_2113, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_493])).
% 6.51/2.32  tff(c_46, plain, (![E_48, D_46, C_45, A_43, B_44]: (k1_xboole_0=C_45 | v2_funct_1(D_46) | ~v2_funct_1(k1_partfun1(A_43, B_44, B_44, C_45, D_46, E_48)) | ~m1_subset_1(E_48, k1_zfmisc_1(k2_zfmisc_1(B_44, C_45))) | ~v1_funct_2(E_48, B_44, C_45) | ~v1_funct_1(E_48) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_funct_2(D_46, A_43, B_44) | ~v1_funct_1(D_46))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.51/2.32  tff(c_3679, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2113, c_46])).
% 6.51/2.32  tff(c_3686, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_52, c_64, c_3679])).
% 6.51/2.32  tff(c_3687, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_76, c_3686])).
% 6.51/2.32  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.51/2.32  tff(c_3725, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3687, c_6])).
% 6.51/2.32  tff(c_3727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_289, c_3725])).
% 6.51/2.32  tff(c_3729, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_235])).
% 6.51/2.32  tff(c_3730, plain, (![A_267]: (~r2_hidden(A_267, '#skF_5'))), inference(splitRight, [status(thm)], [c_235])).
% 6.51/2.32  tff(c_3735, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_3730])).
% 6.51/2.32  tff(c_8, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.51/2.32  tff(c_3903, plain, (![A_278]: (A_278='#skF_5' | ~v1_xboole_0(A_278))), inference(resolution, [status(thm)], [c_3735, c_8])).
% 6.51/2.32  tff(c_3916, plain, (k2_zfmisc_1('#skF_3', '#skF_2')='#skF_5'), inference(resolution, [status(thm)], [c_3729, c_3903])).
% 6.51/2.32  tff(c_3922, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3916, c_52])).
% 6.51/2.32  tff(c_4036, plain, (![D_289, C_290, A_291, B_292]: (D_289=C_290 | ~r2_relset_1(A_291, B_292, C_290, D_289) | ~m1_subset_1(D_289, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))) | ~m1_subset_1(C_290, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.51/2.32  tff(c_4042, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_50, c_4036])).
% 6.51/2.32  tff(c_4053, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_4042])).
% 6.51/2.32  tff(c_4056, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_4053])).
% 6.51/2.32  tff(c_4327, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_4056])).
% 6.51/2.32  tff(c_4331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_56, c_3922, c_3916, c_4327])).
% 6.51/2.32  tff(c_4332, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_4053])).
% 6.51/2.32  tff(c_78, plain, (![B_56, A_57]: (~v1_xboole_0(B_56) | B_56=A_57 | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.51/2.32  tff(c_84, plain, (![A_57]: (k1_xboole_0=A_57 | ~v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_6, c_78])).
% 6.51/2.32  tff(c_3747, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3735, c_84])).
% 6.51/2.32  tff(c_4718, plain, (![A_375, E_372, D_374, C_373, B_376]: (C_373='#skF_5' | v2_funct_1(D_374) | ~v2_funct_1(k1_partfun1(A_375, B_376, B_376, C_373, D_374, E_372)) | ~m1_subset_1(E_372, k1_zfmisc_1(k2_zfmisc_1(B_376, C_373))) | ~v1_funct_2(E_372, B_376, C_373) | ~v1_funct_1(E_372) | ~m1_subset_1(D_374, k1_zfmisc_1(k2_zfmisc_1(A_375, B_376))) | ~v1_funct_2(D_374, A_375, B_376) | ~v1_funct_1(D_374))), inference(demodulation, [status(thm), theory('equality')], [c_3747, c_46])).
% 6.51/2.32  tff(c_4720, plain, ('#skF_5'='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4332, c_4718])).
% 6.51/2.32  tff(c_4722, plain, ('#skF_5'='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_3922, c_3916, c_64, c_4720])).
% 6.51/2.32  tff(c_4723, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_76, c_4722])).
% 6.51/2.32  tff(c_4752, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4723, c_3735])).
% 6.51/2.32  tff(c_4758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3849, c_4752])).
% 6.51/2.32  tff(c_4761, plain, (![A_377]: (~r2_hidden(A_377, '#skF_4'))), inference(splitRight, [status(thm)], [c_236])).
% 6.51/2.32  tff(c_4766, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_4761])).
% 6.51/2.32  tff(c_4773, plain, (![A_378]: (A_378='#skF_5' | ~v1_xboole_0(A_378))), inference(resolution, [status(thm)], [c_3735, c_8])).
% 6.51/2.32  tff(c_4793, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_4766, c_4773])).
% 6.51/2.32  tff(c_100, plain, (![A_60, B_61]: (v1_xboole_0(k2_zfmisc_1(A_60, B_61)) | ~v1_xboole_0(B_61))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.51/2.32  tff(c_134, plain, (![A_65, B_66]: (k2_zfmisc_1(A_65, B_66)=k1_xboole_0 | ~v1_xboole_0(B_66))), inference(resolution, [status(thm)], [c_100, c_84])).
% 6.51/2.32  tff(c_143, plain, (![A_65]: (k2_zfmisc_1(A_65, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_134])).
% 6.51/2.32  tff(c_168, plain, (![A_68]: (m1_subset_1(k6_partfun1(A_68), k1_zfmisc_1(k2_zfmisc_1(A_68, A_68))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30])).
% 6.51/2.32  tff(c_172, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_143, c_168])).
% 6.51/2.32  tff(c_224, plain, (![A_80]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_80, k6_partfun1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_172, c_222])).
% 6.51/2.32  tff(c_237, plain, (![A_81]: (~r2_hidden(A_81, k6_partfun1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_224])).
% 6.51/2.32  tff(c_242, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_237])).
% 6.51/2.32  tff(c_254, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_242, c_84])).
% 6.51/2.32  tff(c_270, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_254, c_64])).
% 6.51/2.32  tff(c_3768, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3747, c_270])).
% 6.51/2.32  tff(c_4805, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4793, c_3768])).
% 6.51/2.32  tff(c_4816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_4805])).
% 6.51/2.32  tff(c_4817, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 6.51/2.32  tff(c_4920, plain, (![C_394, A_395, B_396]: (v1_relat_1(C_394) | ~m1_subset_1(C_394, k1_zfmisc_1(k2_zfmisc_1(A_395, B_396))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.51/2.32  tff(c_4935, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_4920])).
% 6.51/2.32  tff(c_5053, plain, (![C_408, B_409, A_410]: (v5_relat_1(C_408, B_409) | ~m1_subset_1(C_408, k1_zfmisc_1(k2_zfmisc_1(A_410, B_409))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.51/2.32  tff(c_5070, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_5053])).
% 6.51/2.32  tff(c_5136, plain, (![A_420, B_421, C_422]: (k2_relset_1(A_420, B_421, C_422)=k2_relat_1(C_422) | ~m1_subset_1(C_422, k1_zfmisc_1(k2_zfmisc_1(A_420, B_421))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.51/2.32  tff(c_5153, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_5136])).
% 6.51/2.32  tff(c_6727, plain, (![A_512, B_513, C_514, D_515]: (k2_relset_1(A_512, B_513, C_514)=B_513 | ~r2_relset_1(B_513, B_513, k1_partfun1(B_513, A_512, A_512, B_513, D_515, C_514), k6_partfun1(B_513)) | ~m1_subset_1(D_515, k1_zfmisc_1(k2_zfmisc_1(B_513, A_512))) | ~v1_funct_2(D_515, B_513, A_512) | ~v1_funct_1(D_515) | ~m1_subset_1(C_514, k1_zfmisc_1(k2_zfmisc_1(A_512, B_513))) | ~v1_funct_2(C_514, A_512, B_513) | ~v1_funct_1(C_514))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.51/2.32  tff(c_6745, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_6727])).
% 6.51/2.32  tff(c_6749, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_62, c_60, c_58, c_5153, c_6745])).
% 6.51/2.32  tff(c_32, plain, (![B_30]: (v2_funct_2(B_30, k2_relat_1(B_30)) | ~v5_relat_1(B_30, k2_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.51/2.32  tff(c_6754, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6749, c_32])).
% 6.51/2.32  tff(c_6758, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4935, c_5070, c_6749, c_6754])).
% 6.51/2.32  tff(c_6760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4817, c_6758])).
% 6.51/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.51/2.32  
% 6.51/2.32  Inference rules
% 6.51/2.32  ----------------------
% 6.51/2.32  #Ref     : 0
% 6.51/2.32  #Sup     : 1682
% 6.51/2.32  #Fact    : 0
% 6.51/2.32  #Define  : 0
% 6.51/2.32  #Split   : 16
% 6.51/2.32  #Chain   : 0
% 6.51/2.32  #Close   : 0
% 6.51/2.32  
% 6.51/2.32  Ordering : KBO
% 6.51/2.32  
% 6.51/2.32  Simplification rules
% 6.51/2.32  ----------------------
% 6.51/2.32  #Subsume      : 243
% 6.51/2.32  #Demod        : 1195
% 6.51/2.32  #Tautology    : 819
% 6.51/2.32  #SimpNegUnit  : 6
% 6.51/2.32  #BackRed      : 106
% 6.51/2.32  
% 6.51/2.32  #Partial instantiations: 0
% 6.51/2.32  #Strategies tried      : 1
% 6.51/2.32  
% 6.51/2.32  Timing (in seconds)
% 6.51/2.32  ----------------------
% 6.51/2.32  Preprocessing        : 0.35
% 6.51/2.32  Parsing              : 0.19
% 6.51/2.32  CNF conversion       : 0.02
% 6.51/2.32  Main loop            : 1.11
% 6.51/2.33  Inferencing          : 0.35
% 6.51/2.33  Reduction            : 0.38
% 6.51/2.33  Demodulation         : 0.28
% 6.51/2.33  BG Simplification    : 0.04
% 6.51/2.33  Subsumption          : 0.23
% 6.51/2.33  Abstraction          : 0.05
% 6.51/2.33  MUC search           : 0.00
% 6.51/2.33  Cooper               : 0.00
% 6.51/2.33  Total                : 1.51
% 6.51/2.33  Index Insertion      : 0.00
% 6.51/2.33  Index Deletion       : 0.00
% 6.51/2.33  Index Matching       : 0.00
% 6.51/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
