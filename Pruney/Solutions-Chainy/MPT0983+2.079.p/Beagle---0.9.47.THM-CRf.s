%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:12 EST 2020

% Result     : Theorem 6.49s
% Output     : CNFRefutation 6.49s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 215 expanded)
%              Number of leaves         :   46 (  97 expanded)
%              Depth                    :   12
%              Number of atoms          :  195 ( 626 expanded)
%              Number of equality atoms :   29 (  47 expanded)
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

tff(f_166,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_107,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_146,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_124,axiom,(
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

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_52,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_81,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

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

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_201,plain,(
    ! [C_74,B_75,A_76] :
      ( ~ v1_xboole_0(C_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(C_74))
      | ~ r2_hidden(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_215,plain,(
    ! [A_76] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_76,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_201])).

tff(c_280,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_292,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_280])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_44,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_18,plain,(
    ! [A_14] : v2_funct_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67,plain,(
    ! [A_14] : v2_funct_1(k6_partfun1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_18])).

tff(c_36,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,F_35] :
      ( m1_subset_1(k1_partfun1(A_30,B_31,C_32,D_33,E_34,F_35),k1_zfmisc_1(k2_zfmisc_1(A_30,D_33)))
      | ~ m1_subset_1(F_35,k1_zfmisc_1(k2_zfmisc_1(C_32,D_33)))
      | ~ v1_funct_1(F_35)
      | ~ m1_subset_1(E_34,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_1(E_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_54,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1985,plain,(
    ! [D_194,C_195,A_196,B_197] :
      ( D_194 = C_195
      | ~ r2_relset_1(A_196,B_197,C_195,D_194)
      | ~ m1_subset_1(D_194,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1995,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_1985])).

tff(c_2014,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1995])).

tff(c_3592,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2014])).

tff(c_3784,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_3592])).

tff(c_3788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_3784])).

tff(c_3789,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2014])).

tff(c_50,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_3912,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3789,c_50])).

tff(c_3921,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_56,c_67,c_3912])).

tff(c_3922,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_3921])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3964,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3922,c_6])).

tff(c_3966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_3964])).

tff(c_3969,plain,(
    ! [A_300] : ~ r2_hidden(A_300,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_3974,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_3969])).

tff(c_90,plain,(
    ! [B_61,A_62] :
      ( ~ v1_xboole_0(B_61)
      | B_61 = A_62
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_99,plain,(
    ! [A_62] :
      ( k1_xboole_0 = A_62
      | ~ v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_3986,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3974,c_99])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( v1_xboole_0(k2_zfmisc_1(A_7,B_8))
      | ~ v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_100,plain,(
    ! [A_63] :
      ( k1_xboole_0 = A_63
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_114,plain,(
    ! [A_64,B_65] :
      ( k2_zfmisc_1(A_64,B_65) = k1_xboole_0
      | ~ v1_xboole_0(B_65) ) ),
    inference(resolution,[status(thm)],[c_10,c_100])).

tff(c_123,plain,(
    ! [A_64] : k2_zfmisc_1(A_64,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_114])).

tff(c_174,plain,(
    ! [A_70] : m1_subset_1(k6_partfun1(A_70),k1_zfmisc_1(k2_zfmisc_1(A_70,A_70))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_182,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_174])).

tff(c_203,plain,(
    ! [A_76] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_76,k6_partfun1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_182,c_201])).

tff(c_216,plain,(
    ! [A_77] : ~ r2_hidden(A_77,k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_203])).

tff(c_221,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_216])).

tff(c_233,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_221,c_99])).

tff(c_247,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_67])).

tff(c_3990,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3986,c_247])).

tff(c_4000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_3990])).

tff(c_4001,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_4105,plain,(
    ! [C_318,A_319,B_320] :
      ( v1_relat_1(C_318)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_319,B_320))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4122,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_4105])).

tff(c_4129,plain,(
    ! [C_322,B_323,A_324] :
      ( v5_relat_1(C_322,B_323)
      | ~ m1_subset_1(C_322,k1_zfmisc_1(k2_zfmisc_1(A_324,B_323))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4147,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_4129])).

tff(c_4318,plain,(
    ! [A_342,B_343,C_344] :
      ( k2_relset_1(A_342,B_343,C_344) = k2_relat_1(C_344)
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_342,B_343))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4336,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_4318])).

tff(c_7556,plain,(
    ! [A_519,B_520,C_521,D_522] :
      ( k2_relset_1(A_519,B_520,C_521) = B_520
      | ~ r2_relset_1(B_520,B_520,k1_partfun1(B_520,A_519,A_519,B_520,D_522,C_521),k6_partfun1(B_520))
      | ~ m1_subset_1(D_522,k1_zfmisc_1(k2_zfmisc_1(B_520,A_519)))
      | ~ v1_funct_2(D_522,B_520,A_519)
      | ~ v1_funct_1(D_522)
      | ~ m1_subset_1(C_521,k1_zfmisc_1(k2_zfmisc_1(A_519,B_520)))
      | ~ v1_funct_2(C_521,A_519,B_520)
      | ~ v1_funct_1(C_521) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_7574,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_7556])).

tff(c_7578,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_66,c_64,c_62,c_4336,c_7574])).

tff(c_32,plain,(
    ! [B_29] :
      ( v2_funct_2(B_29,k2_relat_1(B_29))
      | ~ v5_relat_1(B_29,k2_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_7583,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7578,c_32])).

tff(c_7587,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4122,c_4147,c_7578,c_7583])).

tff(c_7589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4001,c_7587])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:54:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.49/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.49/2.28  
% 6.49/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.49/2.28  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 6.49/2.28  
% 6.49/2.28  %Foreground sorts:
% 6.49/2.28  
% 6.49/2.28  
% 6.49/2.28  %Background operators:
% 6.49/2.28  
% 6.49/2.28  
% 6.49/2.28  %Foreground operators:
% 6.49/2.28  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.49/2.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.49/2.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.49/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.49/2.28  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.49/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.49/2.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.49/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.49/2.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.49/2.28  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.49/2.28  tff('#skF_5', type, '#skF_5': $i).
% 6.49/2.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.49/2.28  tff('#skF_2', type, '#skF_2': $i).
% 6.49/2.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.49/2.28  tff('#skF_3', type, '#skF_3': $i).
% 6.49/2.28  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.49/2.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.49/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.49/2.28  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.49/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.49/2.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.49/2.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.49/2.28  tff('#skF_4', type, '#skF_4': $i).
% 6.49/2.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.49/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.49/2.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.49/2.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.49/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.49/2.28  
% 6.49/2.30  tff(f_166, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 6.49/2.30  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.49/2.30  tff(f_48, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 6.49/2.30  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 6.49/2.30  tff(f_107, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.49/2.30  tff(f_59, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.49/2.30  tff(f_101, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.49/2.30  tff(f_105, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.49/2.30  tff(f_81, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.49/2.30  tff(f_146, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 6.49/2.30  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.49/2.30  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 6.49/2.30  tff(f_44, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 6.49/2.30  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.49/2.30  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.49/2.30  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.49/2.30  tff(f_124, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 6.49/2.30  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.49/2.30  tff(c_52, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.49/2.30  tff(c_81, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 6.49/2.30  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.49/2.30  tff(c_12, plain, (![A_9, B_10]: (v1_xboole_0(k2_zfmisc_1(A_9, B_10)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.49/2.30  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.49/2.30  tff(c_201, plain, (![C_74, B_75, A_76]: (~v1_xboole_0(C_74) | ~m1_subset_1(B_75, k1_zfmisc_1(C_74)) | ~r2_hidden(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.49/2.30  tff(c_215, plain, (![A_76]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_76, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_201])).
% 6.49/2.30  tff(c_280, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_215])).
% 6.49/2.30  tff(c_292, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_280])).
% 6.49/2.30  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.49/2.30  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.49/2.30  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.49/2.30  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.49/2.30  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.49/2.30  tff(c_44, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.49/2.30  tff(c_18, plain, (![A_14]: (v2_funct_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.49/2.30  tff(c_67, plain, (![A_14]: (v2_funct_1(k6_partfun1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_18])).
% 6.49/2.30  tff(c_36, plain, (![D_33, A_30, C_32, B_31, E_34, F_35]: (m1_subset_1(k1_partfun1(A_30, B_31, C_32, D_33, E_34, F_35), k1_zfmisc_1(k2_zfmisc_1(A_30, D_33))) | ~m1_subset_1(F_35, k1_zfmisc_1(k2_zfmisc_1(C_32, D_33))) | ~v1_funct_1(F_35) | ~m1_subset_1(E_34, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_1(E_34))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.49/2.30  tff(c_42, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.49/2.30  tff(c_54, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.49/2.30  tff(c_1985, plain, (![D_194, C_195, A_196, B_197]: (D_194=C_195 | ~r2_relset_1(A_196, B_197, C_195, D_194) | ~m1_subset_1(D_194, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.49/2.30  tff(c_1995, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_1985])).
% 6.49/2.30  tff(c_2014, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1995])).
% 6.49/2.30  tff(c_3592, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2014])).
% 6.49/2.30  tff(c_3784, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_3592])).
% 6.49/2.30  tff(c_3788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_3784])).
% 6.49/2.30  tff(c_3789, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2014])).
% 6.49/2.30  tff(c_50, plain, (![E_48, D_46, C_45, A_43, B_44]: (k1_xboole_0=C_45 | v2_funct_1(D_46) | ~v2_funct_1(k1_partfun1(A_43, B_44, B_44, C_45, D_46, E_48)) | ~m1_subset_1(E_48, k1_zfmisc_1(k2_zfmisc_1(B_44, C_45))) | ~v1_funct_2(E_48, B_44, C_45) | ~v1_funct_1(E_48) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_funct_2(D_46, A_43, B_44) | ~v1_funct_1(D_46))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.49/2.30  tff(c_3912, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3789, c_50])).
% 6.49/2.30  tff(c_3921, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_56, c_67, c_3912])).
% 6.49/2.30  tff(c_3922, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_81, c_3921])).
% 6.49/2.30  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.49/2.30  tff(c_3964, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3922, c_6])).
% 6.49/2.30  tff(c_3966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_292, c_3964])).
% 6.49/2.30  tff(c_3969, plain, (![A_300]: (~r2_hidden(A_300, '#skF_4'))), inference(splitRight, [status(thm)], [c_215])).
% 6.49/2.30  tff(c_3974, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_3969])).
% 6.49/2.30  tff(c_90, plain, (![B_61, A_62]: (~v1_xboole_0(B_61) | B_61=A_62 | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.49/2.30  tff(c_99, plain, (![A_62]: (k1_xboole_0=A_62 | ~v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_6, c_90])).
% 6.49/2.30  tff(c_3986, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_3974, c_99])).
% 6.49/2.30  tff(c_10, plain, (![A_7, B_8]: (v1_xboole_0(k2_zfmisc_1(A_7, B_8)) | ~v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.49/2.30  tff(c_100, plain, (![A_63]: (k1_xboole_0=A_63 | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_6, c_90])).
% 6.49/2.30  tff(c_114, plain, (![A_64, B_65]: (k2_zfmisc_1(A_64, B_65)=k1_xboole_0 | ~v1_xboole_0(B_65))), inference(resolution, [status(thm)], [c_10, c_100])).
% 6.49/2.30  tff(c_123, plain, (![A_64]: (k2_zfmisc_1(A_64, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_114])).
% 6.49/2.30  tff(c_174, plain, (![A_70]: (m1_subset_1(k6_partfun1(A_70), k1_zfmisc_1(k2_zfmisc_1(A_70, A_70))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.49/2.30  tff(c_182, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_123, c_174])).
% 6.49/2.30  tff(c_203, plain, (![A_76]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_76, k6_partfun1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_182, c_201])).
% 6.49/2.30  tff(c_216, plain, (![A_77]: (~r2_hidden(A_77, k6_partfun1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_203])).
% 6.49/2.30  tff(c_221, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_216])).
% 6.49/2.30  tff(c_233, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_221, c_99])).
% 6.49/2.30  tff(c_247, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_233, c_67])).
% 6.49/2.30  tff(c_3990, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3986, c_247])).
% 6.49/2.30  tff(c_4000, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_3990])).
% 6.49/2.30  tff(c_4001, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 6.49/2.30  tff(c_4105, plain, (![C_318, A_319, B_320]: (v1_relat_1(C_318) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_319, B_320))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.49/2.30  tff(c_4122, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_4105])).
% 6.49/2.30  tff(c_4129, plain, (![C_322, B_323, A_324]: (v5_relat_1(C_322, B_323) | ~m1_subset_1(C_322, k1_zfmisc_1(k2_zfmisc_1(A_324, B_323))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.49/2.30  tff(c_4147, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_4129])).
% 6.49/2.30  tff(c_4318, plain, (![A_342, B_343, C_344]: (k2_relset_1(A_342, B_343, C_344)=k2_relat_1(C_344) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_342, B_343))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.49/2.30  tff(c_4336, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_4318])).
% 6.49/2.30  tff(c_7556, plain, (![A_519, B_520, C_521, D_522]: (k2_relset_1(A_519, B_520, C_521)=B_520 | ~r2_relset_1(B_520, B_520, k1_partfun1(B_520, A_519, A_519, B_520, D_522, C_521), k6_partfun1(B_520)) | ~m1_subset_1(D_522, k1_zfmisc_1(k2_zfmisc_1(B_520, A_519))) | ~v1_funct_2(D_522, B_520, A_519) | ~v1_funct_1(D_522) | ~m1_subset_1(C_521, k1_zfmisc_1(k2_zfmisc_1(A_519, B_520))) | ~v1_funct_2(C_521, A_519, B_520) | ~v1_funct_1(C_521))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.49/2.30  tff(c_7574, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_7556])).
% 6.49/2.30  tff(c_7578, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_66, c_64, c_62, c_4336, c_7574])).
% 6.49/2.30  tff(c_32, plain, (![B_29]: (v2_funct_2(B_29, k2_relat_1(B_29)) | ~v5_relat_1(B_29, k2_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.49/2.30  tff(c_7583, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7578, c_32])).
% 6.49/2.30  tff(c_7587, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4122, c_4147, c_7578, c_7583])).
% 6.49/2.30  tff(c_7589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4001, c_7587])).
% 6.49/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.49/2.30  
% 6.49/2.30  Inference rules
% 6.49/2.30  ----------------------
% 6.49/2.30  #Ref     : 0
% 6.71/2.30  #Sup     : 1923
% 6.71/2.30  #Fact    : 0
% 6.71/2.30  #Define  : 0
% 6.71/2.30  #Split   : 13
% 6.71/2.30  #Chain   : 0
% 6.71/2.30  #Close   : 0
% 6.71/2.30  
% 6.71/2.30  Ordering : KBO
% 6.71/2.30  
% 6.71/2.30  Simplification rules
% 6.71/2.30  ----------------------
% 6.71/2.30  #Subsume      : 246
% 6.71/2.30  #Demod        : 1263
% 6.71/2.30  #Tautology    : 1003
% 6.71/2.30  #SimpNegUnit  : 5
% 6.71/2.30  #BackRed      : 59
% 6.71/2.30  
% 6.71/2.30  #Partial instantiations: 0
% 6.71/2.30  #Strategies tried      : 1
% 6.71/2.30  
% 6.71/2.30  Timing (in seconds)
% 6.71/2.30  ----------------------
% 6.71/2.30  Preprocessing        : 0.35
% 6.71/2.30  Parsing              : 0.19
% 6.71/2.30  CNF conversion       : 0.02
% 6.71/2.30  Main loop            : 1.18
% 6.71/2.30  Inferencing          : 0.36
% 6.71/2.30  Reduction            : 0.42
% 6.71/2.30  Demodulation         : 0.31
% 6.71/2.30  BG Simplification    : 0.05
% 6.71/2.30  Subsumption          : 0.25
% 6.71/2.30  Abstraction          : 0.05
% 6.71/2.30  MUC search           : 0.00
% 6.71/2.30  Cooper               : 0.00
% 6.71/2.30  Total                : 1.56
% 6.71/2.30  Index Insertion      : 0.00
% 6.71/2.30  Index Deletion       : 0.00
% 6.71/2.30  Index Matching       : 0.00
% 6.71/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
