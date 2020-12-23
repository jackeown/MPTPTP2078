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
% DateTime   : Thu Dec  3 10:12:12 EST 2020

% Result     : Theorem 5.35s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 206 expanded)
%              Number of leaves         :   45 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :  187 ( 608 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_158,negated_conjecture,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_99,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_138,axiom,(
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

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_116,axiom,(
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

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_50,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_85,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( v1_xboole_0(k2_zfmisc_1(A_6,B_7))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_181,plain,(
    ! [C_75,B_76,A_77] :
      ( ~ v1_xboole_0(C_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(C_75))
      | ~ r2_hidden(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_195,plain,(
    ! [A_77] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_77,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_181])).

tff(c_254,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_262,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_254])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_42,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_16,plain,(
    ! [A_11] : v2_funct_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_65,plain,(
    ! [A_11] : v2_funct_1(k6_partfun1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_16])).

tff(c_34,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1(k1_partfun1(A_27,B_28,C_29,D_30,E_31,F_32),k1_zfmisc_1(k2_zfmisc_1(A_27,D_30)))
      | ~ m1_subset_1(F_32,k1_zfmisc_1(k2_zfmisc_1(C_29,D_30)))
      | ~ v1_funct_1(F_32)
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_1(E_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_40,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_466,plain,(
    ! [D_101,C_102,A_103,B_104] :
      ( D_101 = C_102
      | ~ r2_relset_1(A_103,B_104,C_102,D_101)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_476,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_52,c_466])).

tff(c_495,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_476])).

tff(c_1243,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_495])).

tff(c_1948,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_1243])).

tff(c_1952,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_58,c_54,c_1948])).

tff(c_1953,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_495])).

tff(c_48,plain,(
    ! [C_42,A_40,D_43,E_45,B_41] :
      ( k1_xboole_0 = C_42
      | v2_funct_1(D_43)
      | ~ v2_funct_1(k1_partfun1(A_40,B_41,B_41,C_42,D_43,E_45))
      | ~ m1_subset_1(E_45,k1_zfmisc_1(k2_zfmisc_1(B_41,C_42)))
      | ~ v1_funct_2(E_45,B_41,C_42)
      | ~ v1_funct_1(E_45)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_2(D_43,A_40,B_41)
      | ~ v1_funct_1(D_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2662,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1953,c_48])).

tff(c_2669,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_56,c_54,c_65,c_2662])).

tff(c_2670,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_2669])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2714,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2670,c_6])).

tff(c_2716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_2714])).

tff(c_2719,plain,(
    ! [A_193] : ~ r2_hidden(A_193,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_2724,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_2719])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2731,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2724,c_8])).

tff(c_92,plain,(
    ! [A_55,B_56] :
      ( v1_xboole_0(k2_zfmisc_1(A_55,B_56))
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_97,plain,(
    ! [A_57,B_58] :
      ( k2_zfmisc_1(A_57,B_58) = k1_xboole_0
      | ~ v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_92,c_8])).

tff(c_103,plain,(
    ! [B_58] : k2_zfmisc_1(k1_xboole_0,B_58) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_97])).

tff(c_116,plain,(
    ! [A_60] : m1_subset_1(k6_partfun1(A_60),k1_zfmisc_1(k2_zfmisc_1(A_60,A_60))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_120,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_116])).

tff(c_183,plain,(
    ! [A_77] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_77,k6_partfun1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_120,c_181])).

tff(c_197,plain,(
    ! [A_79] : ~ r2_hidden(A_79,k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_183])).

tff(c_202,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_197])).

tff(c_209,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_202,c_8])).

tff(c_230,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_65])).

tff(c_2737,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2731,c_230])).

tff(c_2747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_2737])).

tff(c_2748,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2785,plain,(
    ! [C_203,A_204,B_205] :
      ( v1_relat_1(C_203)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2800,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_2785])).

tff(c_2926,plain,(
    ! [C_219,B_220,A_221] :
      ( v5_relat_1(C_219,B_220)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_221,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2944,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_2926])).

tff(c_3044,plain,(
    ! [A_235,B_236,C_237] :
      ( k2_relset_1(A_235,B_236,C_237) = k2_relat_1(C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3062,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_3044])).

tff(c_4725,plain,(
    ! [A_321,B_322,C_323,D_324] :
      ( k2_relset_1(A_321,B_322,C_323) = B_322
      | ~ r2_relset_1(B_322,B_322,k1_partfun1(B_322,A_321,A_321,B_322,D_324,C_323),k6_partfun1(B_322))
      | ~ m1_subset_1(D_324,k1_zfmisc_1(k2_zfmisc_1(B_322,A_321)))
      | ~ v1_funct_2(D_324,B_322,A_321)
      | ~ v1_funct_1(D_324)
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_321,B_322)))
      | ~ v1_funct_2(C_323,A_321,B_322)
      | ~ v1_funct_1(C_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4746,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_4725])).

tff(c_4750,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_64,c_62,c_60,c_3062,c_4746])).

tff(c_30,plain,(
    ! [B_26] :
      ( v2_funct_2(B_26,k2_relat_1(B_26))
      | ~ v5_relat_1(B_26,k2_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4755,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4750,c_30])).

tff(c_4759,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2800,c_2944,c_4750,c_4755])).

tff(c_4761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2748,c_4759])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:05:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.35/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/2.03  
% 5.35/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/2.03  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.35/2.03  
% 5.35/2.03  %Foreground sorts:
% 5.35/2.03  
% 5.35/2.03  
% 5.35/2.03  %Background operators:
% 5.35/2.03  
% 5.35/2.03  
% 5.35/2.03  %Foreground operators:
% 5.35/2.03  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.35/2.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.35/2.03  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.35/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.35/2.03  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.35/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.35/2.03  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.35/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.35/2.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.35/2.03  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.35/2.03  tff('#skF_5', type, '#skF_5': $i).
% 5.35/2.03  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.35/2.03  tff('#skF_2', type, '#skF_2': $i).
% 5.35/2.03  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.35/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.35/2.03  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.35/2.03  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.35/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.35/2.03  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.35/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.35/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.35/2.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.35/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.35/2.03  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.35/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.35/2.03  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.35/2.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.35/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.35/2.03  
% 5.35/2.05  tff(f_158, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 5.35/2.05  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.35/2.05  tff(f_40, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 5.35/2.05  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.35/2.05  tff(f_99, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.35/2.05  tff(f_51, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.35/2.05  tff(f_93, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.35/2.05  tff(f_97, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.35/2.05  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.35/2.05  tff(f_138, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 5.35/2.05  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.35/2.05  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.35/2.05  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.35/2.05  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.35/2.05  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.35/2.05  tff(f_116, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 5.35/2.05  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.35/2.05  tff(c_50, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.35/2.05  tff(c_85, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 5.35/2.05  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.35/2.05  tff(c_10, plain, (![A_6, B_7]: (v1_xboole_0(k2_zfmisc_1(A_6, B_7)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.35/2.05  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.35/2.05  tff(c_181, plain, (![C_75, B_76, A_77]: (~v1_xboole_0(C_75) | ~m1_subset_1(B_76, k1_zfmisc_1(C_75)) | ~r2_hidden(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.35/2.05  tff(c_195, plain, (![A_77]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_77, '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_181])).
% 5.35/2.05  tff(c_254, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_195])).
% 5.35/2.05  tff(c_262, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_10, c_254])).
% 5.35/2.05  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.35/2.05  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.35/2.05  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.35/2.05  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.35/2.05  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.35/2.05  tff(c_42, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.35/2.05  tff(c_16, plain, (![A_11]: (v2_funct_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.35/2.05  tff(c_65, plain, (![A_11]: (v2_funct_1(k6_partfun1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_16])).
% 5.35/2.05  tff(c_34, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1(k1_partfun1(A_27, B_28, C_29, D_30, E_31, F_32), k1_zfmisc_1(k2_zfmisc_1(A_27, D_30))) | ~m1_subset_1(F_32, k1_zfmisc_1(k2_zfmisc_1(C_29, D_30))) | ~v1_funct_1(F_32) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_1(E_31))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.35/2.05  tff(c_40, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.35/2.05  tff(c_52, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.35/2.05  tff(c_466, plain, (![D_101, C_102, A_103, B_104]: (D_101=C_102 | ~r2_relset_1(A_103, B_104, C_102, D_101) | ~m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.35/2.05  tff(c_476, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_52, c_466])).
% 5.35/2.05  tff(c_495, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_476])).
% 5.35/2.05  tff(c_1243, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_495])).
% 5.35/2.05  tff(c_1948, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_1243])).
% 5.35/2.05  tff(c_1952, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_58, c_54, c_1948])).
% 5.35/2.05  tff(c_1953, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_495])).
% 5.35/2.05  tff(c_48, plain, (![C_42, A_40, D_43, E_45, B_41]: (k1_xboole_0=C_42 | v2_funct_1(D_43) | ~v2_funct_1(k1_partfun1(A_40, B_41, B_41, C_42, D_43, E_45)) | ~m1_subset_1(E_45, k1_zfmisc_1(k2_zfmisc_1(B_41, C_42))) | ~v1_funct_2(E_45, B_41, C_42) | ~v1_funct_1(E_45) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_2(D_43, A_40, B_41) | ~v1_funct_1(D_43))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.35/2.05  tff(c_2662, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1953, c_48])).
% 5.35/2.05  tff(c_2669, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_54, c_65, c_2662])).
% 5.35/2.05  tff(c_2670, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_85, c_2669])).
% 5.35/2.05  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.05  tff(c_2714, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2670, c_6])).
% 5.35/2.05  tff(c_2716, plain, $false, inference(negUnitSimplification, [status(thm)], [c_262, c_2714])).
% 5.35/2.05  tff(c_2719, plain, (![A_193]: (~r2_hidden(A_193, '#skF_4'))), inference(splitRight, [status(thm)], [c_195])).
% 5.35/2.05  tff(c_2724, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_2719])).
% 5.35/2.05  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.35/2.05  tff(c_2731, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2724, c_8])).
% 5.35/2.05  tff(c_92, plain, (![A_55, B_56]: (v1_xboole_0(k2_zfmisc_1(A_55, B_56)) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.35/2.05  tff(c_97, plain, (![A_57, B_58]: (k2_zfmisc_1(A_57, B_58)=k1_xboole_0 | ~v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_92, c_8])).
% 5.35/2.05  tff(c_103, plain, (![B_58]: (k2_zfmisc_1(k1_xboole_0, B_58)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_97])).
% 5.35/2.05  tff(c_116, plain, (![A_60]: (m1_subset_1(k6_partfun1(A_60), k1_zfmisc_1(k2_zfmisc_1(A_60, A_60))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.35/2.05  tff(c_120, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_103, c_116])).
% 5.35/2.05  tff(c_183, plain, (![A_77]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_77, k6_partfun1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_120, c_181])).
% 5.35/2.05  tff(c_197, plain, (![A_79]: (~r2_hidden(A_79, k6_partfun1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_183])).
% 5.35/2.05  tff(c_202, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_197])).
% 5.35/2.05  tff(c_209, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_202, c_8])).
% 5.35/2.05  tff(c_230, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_209, c_65])).
% 5.35/2.05  tff(c_2737, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2731, c_230])).
% 5.35/2.05  tff(c_2747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_2737])).
% 5.35/2.05  tff(c_2748, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 5.35/2.05  tff(c_2785, plain, (![C_203, A_204, B_205]: (v1_relat_1(C_203) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.35/2.05  tff(c_2800, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_2785])).
% 5.35/2.05  tff(c_2926, plain, (![C_219, B_220, A_221]: (v5_relat_1(C_219, B_220) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_221, B_220))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.35/2.05  tff(c_2944, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_2926])).
% 5.35/2.05  tff(c_3044, plain, (![A_235, B_236, C_237]: (k2_relset_1(A_235, B_236, C_237)=k2_relat_1(C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.35/2.05  tff(c_3062, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_3044])).
% 5.35/2.05  tff(c_4725, plain, (![A_321, B_322, C_323, D_324]: (k2_relset_1(A_321, B_322, C_323)=B_322 | ~r2_relset_1(B_322, B_322, k1_partfun1(B_322, A_321, A_321, B_322, D_324, C_323), k6_partfun1(B_322)) | ~m1_subset_1(D_324, k1_zfmisc_1(k2_zfmisc_1(B_322, A_321))) | ~v1_funct_2(D_324, B_322, A_321) | ~v1_funct_1(D_324) | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_321, B_322))) | ~v1_funct_2(C_323, A_321, B_322) | ~v1_funct_1(C_323))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.35/2.05  tff(c_4746, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_4725])).
% 5.35/2.05  tff(c_4750, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_64, c_62, c_60, c_3062, c_4746])).
% 5.35/2.05  tff(c_30, plain, (![B_26]: (v2_funct_2(B_26, k2_relat_1(B_26)) | ~v5_relat_1(B_26, k2_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.35/2.05  tff(c_4755, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4750, c_30])).
% 5.35/2.05  tff(c_4759, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2800, c_2944, c_4750, c_4755])).
% 5.35/2.05  tff(c_4761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2748, c_4759])).
% 5.35/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/2.05  
% 5.35/2.05  Inference rules
% 5.35/2.05  ----------------------
% 5.35/2.05  #Ref     : 0
% 5.35/2.05  #Sup     : 1150
% 5.35/2.05  #Fact    : 0
% 5.35/2.05  #Define  : 0
% 5.35/2.05  #Split   : 11
% 5.35/2.05  #Chain   : 0
% 5.35/2.05  #Close   : 0
% 5.35/2.05  
% 5.35/2.05  Ordering : KBO
% 5.35/2.05  
% 5.35/2.05  Simplification rules
% 5.35/2.05  ----------------------
% 5.35/2.05  #Subsume      : 119
% 5.35/2.05  #Demod        : 1253
% 5.35/2.05  #Tautology    : 699
% 5.35/2.05  #SimpNegUnit  : 4
% 5.35/2.05  #BackRed      : 64
% 5.35/2.05  
% 5.35/2.05  #Partial instantiations: 0
% 5.35/2.05  #Strategies tried      : 1
% 5.35/2.05  
% 5.35/2.05  Timing (in seconds)
% 5.35/2.05  ----------------------
% 5.35/2.05  Preprocessing        : 0.35
% 5.35/2.05  Parsing              : 0.18
% 5.35/2.05  CNF conversion       : 0.03
% 5.35/2.05  Main loop            : 0.91
% 5.35/2.05  Inferencing          : 0.29
% 5.35/2.05  Reduction            : 0.34
% 5.35/2.05  Demodulation         : 0.25
% 5.35/2.05  BG Simplification    : 0.04
% 5.35/2.05  Subsumption          : 0.18
% 5.35/2.05  Abstraction          : 0.04
% 5.35/2.05  MUC search           : 0.00
% 5.35/2.05  Cooper               : 0.00
% 5.35/2.05  Total                : 1.29
% 5.35/2.05  Index Insertion      : 0.00
% 5.35/2.05  Index Deletion       : 0.00
% 5.35/2.05  Index Matching       : 0.00
% 5.35/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
