%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:13 EST 2020

% Result     : Theorem 5.89s
% Output     : CNFRefutation 6.24s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 251 expanded)
%              Number of leaves         :   45 ( 110 expanded)
%              Depth                    :   11
%              Number of atoms          :  206 ( 745 expanded)
%              Number of equality atoms :   31 (  60 expanded)
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

tff(f_156,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_97,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_91,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_136,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_114,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_48,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_81,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

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

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_150,plain,(
    ! [C_68,B_69,A_70] :
      ( ~ v1_xboole_0(C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_163,plain,(
    ! [A_70] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_70,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_150])).

tff(c_223,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_231,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_223])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_40,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_14,plain,(
    ! [A_11] : v2_funct_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63,plain,(
    ! [A_11] : v2_funct_1(k6_partfun1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_32,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1(k1_partfun1(A_27,B_28,C_29,D_30,E_31,F_32),k1_zfmisc_1(k2_zfmisc_1(A_27,D_30)))
      | ~ m1_subset_1(F_32,k1_zfmisc_1(k2_zfmisc_1(C_29,D_30)))
      | ~ v1_funct_1(F_32)
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_1(E_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_38,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_465,plain,(
    ! [D_101,C_102,A_103,B_104] :
      ( D_101 = C_102
      | ~ r2_relset_1(A_103,B_104,C_102,D_101)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_475,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_50,c_465])).

tff(c_494,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_475])).

tff(c_1379,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_494])).

tff(c_1987,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1379])).

tff(c_1991,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_52,c_1987])).

tff(c_1992,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_494])).

tff(c_46,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2604,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1992,c_46])).

tff(c_2611,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_52,c_63,c_2604])).

tff(c_2612,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_2611])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2657,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2612,c_6])).

tff(c_2659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_2657])).

tff(c_2662,plain,(
    ! [A_192] : ~ r2_hidden(A_192,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_2667,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_2662])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2674,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2667,c_8])).

tff(c_83,plain,(
    ! [A_53,B_54] :
      ( v1_xboole_0(k2_zfmisc_1(A_53,B_54))
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_93,plain,(
    ! [A_56,B_57] :
      ( k2_zfmisc_1(A_56,B_57) = k1_xboole_0
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_83,c_8])).

tff(c_99,plain,(
    ! [B_57] : k2_zfmisc_1(k1_xboole_0,B_57) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_112,plain,(
    ! [A_59] : m1_subset_1(k6_partfun1(A_59),k1_zfmisc_1(k2_zfmisc_1(A_59,A_59))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_116,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_112])).

tff(c_152,plain,(
    ! [A_70] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_70,k6_partfun1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_116,c_150])).

tff(c_165,plain,(
    ! [A_71] : ~ r2_hidden(A_71,k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_152])).

tff(c_170,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_165])).

tff(c_177,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_170,c_8])).

tff(c_195,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_63])).

tff(c_2676,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2674,c_195])).

tff(c_2684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_2676])).

tff(c_2685,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2722,plain,(
    ! [C_202,A_203,B_204] :
      ( v1_relat_1(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2735,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_2722])).

tff(c_2776,plain,(
    ! [C_210,B_211,A_212] :
      ( v5_relat_1(C_210,B_211)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_212,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2793,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2776])).

tff(c_2898,plain,(
    ! [A_224,B_225,D_226] :
      ( r2_relset_1(A_224,B_225,D_226,D_226)
      | ~ m1_subset_1(D_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2909,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_38,c_2898])).

tff(c_2949,plain,(
    ! [A_230,B_231,C_232] :
      ( k2_relset_1(A_230,B_231,C_232) = k2_relat_1(C_232)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_230,B_231))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2966,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_2949])).

tff(c_2983,plain,(
    ! [D_234,C_235,A_236,B_237] :
      ( D_234 = C_235
      | ~ r2_relset_1(A_236,B_237,C_235,D_234)
      | ~ m1_subset_1(D_234,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237)))
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2993,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_50,c_2983])).

tff(c_3012,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2993])).

tff(c_3032,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3012])).

tff(c_4159,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_3032])).

tff(c_4163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_52,c_4159])).

tff(c_4164,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3012])).

tff(c_5696,plain,(
    ! [A_386,B_387,C_388,D_389] :
      ( k2_relset_1(A_386,B_387,C_388) = B_387
      | ~ r2_relset_1(B_387,B_387,k1_partfun1(B_387,A_386,A_386,B_387,D_389,C_388),k6_partfun1(B_387))
      | ~ m1_subset_1(D_389,k1_zfmisc_1(k2_zfmisc_1(B_387,A_386)))
      | ~ v1_funct_2(D_389,B_387,A_386)
      | ~ v1_funct_1(D_389)
      | ~ m1_subset_1(C_388,k1_zfmisc_1(k2_zfmisc_1(A_386,B_387)))
      | ~ v1_funct_2(C_388,A_386,B_387)
      | ~ v1_funct_1(C_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_5702,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4164,c_5696])).

tff(c_5719,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_62,c_60,c_58,c_2909,c_2966,c_5702])).

tff(c_28,plain,(
    ! [B_26] :
      ( v2_funct_2(B_26,k2_relat_1(B_26))
      | ~ v5_relat_1(B_26,k2_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5725,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5719,c_28])).

tff(c_5729,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2735,c_2793,c_5719,c_5725])).

tff(c_5731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2685,c_5729])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:39:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.89/2.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.24/2.22  
% 6.24/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.24/2.22  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 6.24/2.22  
% 6.24/2.22  %Foreground sorts:
% 6.24/2.22  
% 6.24/2.22  
% 6.24/2.22  %Background operators:
% 6.24/2.22  
% 6.24/2.22  
% 6.24/2.22  %Foreground operators:
% 6.24/2.22  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.24/2.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.24/2.22  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.24/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.24/2.22  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.24/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.24/2.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.24/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.24/2.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.24/2.22  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.24/2.22  tff('#skF_5', type, '#skF_5': $i).
% 6.24/2.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.24/2.22  tff('#skF_2', type, '#skF_2': $i).
% 6.24/2.22  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.24/2.22  tff('#skF_3', type, '#skF_3': $i).
% 6.24/2.22  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.24/2.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.24/2.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.24/2.22  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.24/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.24/2.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.24/2.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.24/2.22  tff('#skF_4', type, '#skF_4': $i).
% 6.24/2.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.24/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.24/2.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.24/2.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.24/2.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.24/2.22  
% 6.24/2.25  tff(f_156, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 6.24/2.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.24/2.25  tff(f_40, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 6.24/2.25  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 6.24/2.25  tff(f_97, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.24/2.25  tff(f_49, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 6.24/2.25  tff(f_91, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.24/2.25  tff(f_95, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.24/2.25  tff(f_71, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.24/2.25  tff(f_136, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 6.24/2.25  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.24/2.25  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.24/2.25  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.24/2.25  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.24/2.25  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.24/2.25  tff(f_114, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 6.24/2.25  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.24/2.25  tff(c_48, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.24/2.25  tff(c_81, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 6.24/2.25  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.24/2.25  tff(c_10, plain, (![A_6, B_7]: (v1_xboole_0(k2_zfmisc_1(A_6, B_7)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.24/2.25  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.24/2.25  tff(c_150, plain, (![C_68, B_69, A_70]: (~v1_xboole_0(C_68) | ~m1_subset_1(B_69, k1_zfmisc_1(C_68)) | ~r2_hidden(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.24/2.25  tff(c_163, plain, (![A_70]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_70, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_150])).
% 6.24/2.25  tff(c_223, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_163])).
% 6.24/2.25  tff(c_231, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_10, c_223])).
% 6.24/2.25  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.24/2.25  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.24/2.25  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.24/2.25  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.24/2.25  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.24/2.25  tff(c_40, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.24/2.25  tff(c_14, plain, (![A_11]: (v2_funct_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.24/2.25  tff(c_63, plain, (![A_11]: (v2_funct_1(k6_partfun1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14])).
% 6.24/2.25  tff(c_32, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1(k1_partfun1(A_27, B_28, C_29, D_30, E_31, F_32), k1_zfmisc_1(k2_zfmisc_1(A_27, D_30))) | ~m1_subset_1(F_32, k1_zfmisc_1(k2_zfmisc_1(C_29, D_30))) | ~v1_funct_1(F_32) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_1(E_31))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.24/2.25  tff(c_38, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.24/2.25  tff(c_50, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.24/2.25  tff(c_465, plain, (![D_101, C_102, A_103, B_104]: (D_101=C_102 | ~r2_relset_1(A_103, B_104, C_102, D_101) | ~m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.24/2.25  tff(c_475, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_50, c_465])).
% 6.24/2.25  tff(c_494, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_475])).
% 6.24/2.25  tff(c_1379, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_494])).
% 6.24/2.25  tff(c_1987, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_1379])).
% 6.24/2.25  tff(c_1991, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_56, c_52, c_1987])).
% 6.24/2.25  tff(c_1992, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_494])).
% 6.24/2.25  tff(c_46, plain, (![C_42, A_40, D_43, E_45, B_41]: (k1_xboole_0=C_42 | v2_funct_1(D_43) | ~v2_funct_1(k1_partfun1(A_40, B_41, B_41, C_42, D_43, E_45)) | ~m1_subset_1(E_45, k1_zfmisc_1(k2_zfmisc_1(B_41, C_42))) | ~v1_funct_2(E_45, B_41, C_42) | ~v1_funct_1(E_45) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_2(D_43, A_40, B_41) | ~v1_funct_1(D_43))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.24/2.25  tff(c_2604, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1992, c_46])).
% 6.24/2.25  tff(c_2611, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_52, c_63, c_2604])).
% 6.24/2.25  tff(c_2612, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_81, c_2611])).
% 6.24/2.25  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.24/2.25  tff(c_2657, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2612, c_6])).
% 6.24/2.25  tff(c_2659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_231, c_2657])).
% 6.24/2.25  tff(c_2662, plain, (![A_192]: (~r2_hidden(A_192, '#skF_4'))), inference(splitRight, [status(thm)], [c_163])).
% 6.24/2.25  tff(c_2667, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_2662])).
% 6.24/2.25  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.24/2.25  tff(c_2674, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2667, c_8])).
% 6.24/2.25  tff(c_83, plain, (![A_53, B_54]: (v1_xboole_0(k2_zfmisc_1(A_53, B_54)) | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.24/2.25  tff(c_93, plain, (![A_56, B_57]: (k2_zfmisc_1(A_56, B_57)=k1_xboole_0 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_83, c_8])).
% 6.24/2.25  tff(c_99, plain, (![B_57]: (k2_zfmisc_1(k1_xboole_0, B_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_93])).
% 6.24/2.25  tff(c_112, plain, (![A_59]: (m1_subset_1(k6_partfun1(A_59), k1_zfmisc_1(k2_zfmisc_1(A_59, A_59))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.24/2.25  tff(c_116, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_99, c_112])).
% 6.24/2.25  tff(c_152, plain, (![A_70]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_70, k6_partfun1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_116, c_150])).
% 6.24/2.25  tff(c_165, plain, (![A_71]: (~r2_hidden(A_71, k6_partfun1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_152])).
% 6.24/2.25  tff(c_170, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_165])).
% 6.24/2.25  tff(c_177, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_170, c_8])).
% 6.24/2.25  tff(c_195, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_177, c_63])).
% 6.24/2.25  tff(c_2676, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2674, c_195])).
% 6.24/2.25  tff(c_2684, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_2676])).
% 6.24/2.25  tff(c_2685, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 6.24/2.25  tff(c_2722, plain, (![C_202, A_203, B_204]: (v1_relat_1(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.24/2.25  tff(c_2735, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_2722])).
% 6.24/2.25  tff(c_2776, plain, (![C_210, B_211, A_212]: (v5_relat_1(C_210, B_211) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_212, B_211))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.24/2.25  tff(c_2793, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_2776])).
% 6.24/2.25  tff(c_2898, plain, (![A_224, B_225, D_226]: (r2_relset_1(A_224, B_225, D_226, D_226) | ~m1_subset_1(D_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.24/2.25  tff(c_2909, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_38, c_2898])).
% 6.24/2.25  tff(c_2949, plain, (![A_230, B_231, C_232]: (k2_relset_1(A_230, B_231, C_232)=k2_relat_1(C_232) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_230, B_231))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.24/2.25  tff(c_2966, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_2949])).
% 6.24/2.25  tff(c_2983, plain, (![D_234, C_235, A_236, B_237]: (D_234=C_235 | ~r2_relset_1(A_236, B_237, C_235, D_234) | ~m1_subset_1(D_234, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.24/2.25  tff(c_2993, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_50, c_2983])).
% 6.24/2.25  tff(c_3012, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2993])).
% 6.24/2.25  tff(c_3032, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_3012])).
% 6.24/2.25  tff(c_4159, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_3032])).
% 6.24/2.25  tff(c_4163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_56, c_52, c_4159])).
% 6.24/2.25  tff(c_4164, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_3012])).
% 6.24/2.25  tff(c_5696, plain, (![A_386, B_387, C_388, D_389]: (k2_relset_1(A_386, B_387, C_388)=B_387 | ~r2_relset_1(B_387, B_387, k1_partfun1(B_387, A_386, A_386, B_387, D_389, C_388), k6_partfun1(B_387)) | ~m1_subset_1(D_389, k1_zfmisc_1(k2_zfmisc_1(B_387, A_386))) | ~v1_funct_2(D_389, B_387, A_386) | ~v1_funct_1(D_389) | ~m1_subset_1(C_388, k1_zfmisc_1(k2_zfmisc_1(A_386, B_387))) | ~v1_funct_2(C_388, A_386, B_387) | ~v1_funct_1(C_388))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.24/2.25  tff(c_5702, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4164, c_5696])).
% 6.24/2.25  tff(c_5719, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_62, c_60, c_58, c_2909, c_2966, c_5702])).
% 6.24/2.25  tff(c_28, plain, (![B_26]: (v2_funct_2(B_26, k2_relat_1(B_26)) | ~v5_relat_1(B_26, k2_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.24/2.25  tff(c_5725, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5719, c_28])).
% 6.24/2.25  tff(c_5729, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2735, c_2793, c_5719, c_5725])).
% 6.24/2.25  tff(c_5731, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2685, c_5729])).
% 6.24/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.24/2.25  
% 6.24/2.25  Inference rules
% 6.24/2.25  ----------------------
% 6.24/2.25  #Ref     : 0
% 6.24/2.25  #Sup     : 1394
% 6.24/2.25  #Fact    : 0
% 6.24/2.25  #Define  : 0
% 6.24/2.25  #Split   : 11
% 6.24/2.25  #Chain   : 0
% 6.24/2.25  #Close   : 0
% 6.24/2.25  
% 6.24/2.25  Ordering : KBO
% 6.24/2.25  
% 6.24/2.25  Simplification rules
% 6.24/2.25  ----------------------
% 6.24/2.25  #Subsume      : 142
% 6.24/2.25  #Demod        : 1479
% 6.24/2.25  #Tautology    : 836
% 6.24/2.25  #SimpNegUnit  : 4
% 6.24/2.25  #BackRed      : 61
% 6.24/2.25  
% 6.24/2.25  #Partial instantiations: 0
% 6.24/2.25  #Strategies tried      : 1
% 6.24/2.25  
% 6.24/2.25  Timing (in seconds)
% 6.24/2.25  ----------------------
% 6.24/2.25  Preprocessing        : 0.36
% 6.24/2.25  Parsing              : 0.19
% 6.24/2.25  CNF conversion       : 0.03
% 6.24/2.25  Main loop            : 1.12
% 6.24/2.25  Inferencing          : 0.36
% 6.24/2.25  Reduction            : 0.40
% 6.24/2.25  Demodulation         : 0.29
% 6.24/2.26  BG Simplification    : 0.04
% 6.24/2.26  Subsumption          : 0.22
% 6.24/2.26  Abstraction          : 0.05
% 6.24/2.26  MUC search           : 0.00
% 6.24/2.26  Cooper               : 0.00
% 6.24/2.26  Total                : 1.53
% 6.24/2.26  Index Insertion      : 0.00
% 6.24/2.26  Index Deletion       : 0.00
% 6.24/2.26  Index Matching       : 0.00
% 6.24/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
