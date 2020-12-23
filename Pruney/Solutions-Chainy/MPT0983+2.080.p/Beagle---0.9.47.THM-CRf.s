%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:12 EST 2020

% Result     : Theorem 7.27s
% Output     : CNFRefutation 7.50s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 416 expanded)
%              Number of leaves         :   46 ( 163 expanded)
%              Depth                    :   13
%              Number of atoms          :  251 (1219 expanded)
%              Number of equality atoms :   41 (  94 expanded)
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

tff(f_164,negated_conjecture,(
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

tff(f_105,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_57,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_99,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_144,axiom,(
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

tff(f_122,axiom,(
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

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_50,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_78,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

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

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_244,plain,(
    ! [C_83,B_84,A_85] :
      ( ~ v1_xboole_0(C_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(C_83))
      | ~ r2_hidden(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_257,plain,(
    ! [A_85] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_85,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_244])).

tff(c_5447,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_5471,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_5447])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( v1_xboole_0(k2_zfmisc_1(A_7,B_8))
      | ~ v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_258,plain,(
    ! [A_85] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2'))
      | ~ r2_hidden(A_85,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_244])).

tff(c_311,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_318,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_311])).

tff(c_42,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_16,plain,(
    ! [A_14] : v2_funct_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_65,plain,(
    ! [A_14] : v2_funct_1(k6_partfun1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_16])).

tff(c_34,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,F_35] :
      ( m1_subset_1(k1_partfun1(A_30,B_31,C_32,D_33,E_34,F_35),k1_zfmisc_1(k2_zfmisc_1(A_30,D_33)))
      | ~ m1_subset_1(F_35,k1_zfmisc_1(k2_zfmisc_1(C_32,D_33)))
      | ~ v1_funct_1(F_35)
      | ~ m1_subset_1(E_34,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_1(E_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_52,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_2014,plain,(
    ! [D_197,C_198,A_199,B_200] :
      ( D_197 = C_198
      | ~ r2_relset_1(A_199,B_200,C_198,D_197)
      | ~ m1_subset_1(D_197,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200)))
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2024,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_52,c_2014])).

tff(c_2043,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2024])).

tff(c_2056,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2043])).

tff(c_3512,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_2056])).

tff(c_3516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_58,c_54,c_3512])).

tff(c_3517,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2043])).

tff(c_48,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_5303,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3517,c_48])).

tff(c_5312,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_56,c_54,c_65,c_5303])).

tff(c_5313,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5312])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5356,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5313,c_6])).

tff(c_5358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_318,c_5356])).

tff(c_5360,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_5361,plain,(
    ! [A_375] : ~ r2_hidden(A_375,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_5366,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_5361])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5472,plain,(
    ! [A_381] :
      ( A_381 = '#skF_5'
      | ~ v1_xboole_0(A_381) ) ),
    inference(resolution,[status(thm)],[c_5366,c_8])).

tff(c_5485,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_5360,c_5472])).

tff(c_5584,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5485,c_54])).

tff(c_5621,plain,(
    ! [D_387,C_388,A_389,B_390] :
      ( D_387 = C_388
      | ~ r2_relset_1(A_389,B_390,C_388,D_387)
      | ~ m1_subset_1(D_387,k1_zfmisc_1(k2_zfmisc_1(A_389,B_390)))
      | ~ m1_subset_1(C_388,k1_zfmisc_1(k2_zfmisc_1(A_389,B_390))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5627,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_52,c_5621])).

tff(c_5638,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5627])).

tff(c_6118,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_5638])).

tff(c_6232,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_6118])).

tff(c_6236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_58,c_5584,c_5485,c_6232])).

tff(c_6237,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_5638])).

tff(c_79,plain,(
    ! [B_55,A_56] :
      ( ~ v1_xboole_0(B_55)
      | B_55 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_82,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_5378,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_5366,c_82])).

tff(c_6106,plain,(
    ! [E_48,D_46,C_45,A_43,B_44] :
      ( C_45 = '#skF_5'
      | v2_funct_1(D_46)
      | ~ v2_funct_1(k1_partfun1(A_43,B_44,B_44,C_45,D_46,E_48))
      | ~ m1_subset_1(E_48,k1_zfmisc_1(k2_zfmisc_1(B_44,C_45)))
      | ~ v1_funct_2(E_48,B_44,C_45)
      | ~ v1_funct_1(E_48)
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_funct_2(D_46,A_43,B_44)
      | ~ v1_funct_1(D_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5378,c_48])).

tff(c_6357,plain,
    ( '#skF_5' = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6237,c_6106])).

tff(c_6366,plain,
    ( '#skF_5' = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_56,c_5584,c_5485,c_65,c_6357])).

tff(c_6367,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6366])).

tff(c_6399,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6367,c_5366])).

tff(c_6405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5471,c_6399])).

tff(c_6408,plain,(
    ! [A_508] : ~ r2_hidden(A_508,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_6413,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_6408])).

tff(c_6467,plain,(
    ! [A_513] :
      ( A_513 = '#skF_5'
      | ~ v1_xboole_0(A_513) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5378,c_82])).

tff(c_6488,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6413,c_6467])).

tff(c_97,plain,(
    ! [A_60,B_61] :
      ( v1_xboole_0(k2_zfmisc_1(A_60,B_61))
      | ~ v1_xboole_0(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_136,plain,(
    ! [A_66,B_67] :
      ( k2_zfmisc_1(A_66,B_67) = k1_xboole_0
      | ~ v1_xboole_0(B_67) ) ),
    inference(resolution,[status(thm)],[c_97,c_82])).

tff(c_145,plain,(
    ! [A_66] : k2_zfmisc_1(A_66,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_170,plain,(
    ! [A_69] : m1_subset_1(k6_partfun1(A_69),k1_zfmisc_1(k2_zfmisc_1(A_69,A_69))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_174,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_170])).

tff(c_246,plain,(
    ! [A_85] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_85,k6_partfun1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_174,c_244])).

tff(c_259,plain,(
    ! [A_86] : ~ r2_hidden(A_86,k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_246])).

tff(c_264,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_259])).

tff(c_276,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_264,c_82])).

tff(c_298,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_65])).

tff(c_5383,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5378,c_298])).

tff(c_6499,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_5383])).

tff(c_6511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6499])).

tff(c_6512,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_6615,plain,(
    ! [C_529,A_530,B_531] :
      ( v1_relat_1(C_529)
      | ~ m1_subset_1(C_529,k1_zfmisc_1(k2_zfmisc_1(A_530,B_531))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6630,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_6615])).

tff(c_6639,plain,(
    ! [C_534,B_535,A_536] :
      ( v5_relat_1(C_534,B_535)
      | ~ m1_subset_1(C_534,k1_zfmisc_1(k2_zfmisc_1(A_536,B_535))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6656,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_6639])).

tff(c_6830,plain,(
    ! [A_554,B_555,C_556] :
      ( k2_relset_1(A_554,B_555,C_556) = k2_relat_1(C_556)
      | ~ m1_subset_1(C_556,k1_zfmisc_1(k2_zfmisc_1(A_554,B_555))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6847,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_6830])).

tff(c_8048,plain,(
    ! [A_638,B_639,C_640,D_641] :
      ( k2_relset_1(A_638,B_639,C_640) = B_639
      | ~ r2_relset_1(B_639,B_639,k1_partfun1(B_639,A_638,A_638,B_639,D_641,C_640),k6_partfun1(B_639))
      | ~ m1_subset_1(D_641,k1_zfmisc_1(k2_zfmisc_1(B_639,A_638)))
      | ~ v1_funct_2(D_641,B_639,A_638)
      | ~ v1_funct_1(D_641)
      | ~ m1_subset_1(C_640,k1_zfmisc_1(k2_zfmisc_1(A_638,B_639)))
      | ~ v1_funct_2(C_640,A_638,B_639)
      | ~ v1_funct_1(C_640) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_8066,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_8048])).

tff(c_8070,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_64,c_62,c_60,c_6847,c_8066])).

tff(c_30,plain,(
    ! [B_29] :
      ( v2_funct_2(B_29,k2_relat_1(B_29))
      | ~ v5_relat_1(B_29,k2_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8075,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8070,c_30])).

tff(c_8079,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6630,c_6656,c_8070,c_8075])).

tff(c_8081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6512,c_8079])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.27/2.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.27/2.53  
% 7.27/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.27/2.53  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 7.27/2.53  
% 7.27/2.53  %Foreground sorts:
% 7.27/2.53  
% 7.27/2.53  
% 7.27/2.53  %Background operators:
% 7.27/2.53  
% 7.27/2.53  
% 7.27/2.53  %Foreground operators:
% 7.27/2.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.27/2.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.27/2.53  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.27/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.27/2.53  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.27/2.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.27/2.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.27/2.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.27/2.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.27/2.53  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.27/2.53  tff('#skF_5', type, '#skF_5': $i).
% 7.27/2.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.27/2.53  tff('#skF_2', type, '#skF_2': $i).
% 7.27/2.53  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.27/2.53  tff('#skF_3', type, '#skF_3': $i).
% 7.27/2.53  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.27/2.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.27/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.27/2.53  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.27/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.27/2.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.27/2.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.27/2.53  tff('#skF_4', type, '#skF_4': $i).
% 7.27/2.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.27/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.27/2.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.27/2.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.27/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.27/2.53  
% 7.50/2.55  tff(f_164, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 7.50/2.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.50/2.55  tff(f_48, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 7.50/2.55  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.50/2.55  tff(f_44, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 7.50/2.55  tff(f_105, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.50/2.55  tff(f_57, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 7.50/2.55  tff(f_99, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.50/2.55  tff(f_103, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.50/2.55  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.50/2.55  tff(f_144, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 7.50/2.55  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.50/2.55  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 7.50/2.55  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.50/2.55  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.50/2.55  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.50/2.55  tff(f_122, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.50/2.55  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.50/2.55  tff(c_50, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.50/2.55  tff(c_78, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 7.50/2.55  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.50/2.55  tff(c_12, plain, (![A_9, B_10]: (v1_xboole_0(k2_zfmisc_1(A_9, B_10)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.50/2.55  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.50/2.55  tff(c_244, plain, (![C_83, B_84, A_85]: (~v1_xboole_0(C_83) | ~m1_subset_1(B_84, k1_zfmisc_1(C_83)) | ~r2_hidden(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.50/2.55  tff(c_257, plain, (![A_85]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_85, '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_244])).
% 7.50/2.55  tff(c_5447, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_257])).
% 7.50/2.55  tff(c_5471, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_5447])).
% 7.50/2.55  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.50/2.55  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.50/2.55  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.50/2.55  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.50/2.55  tff(c_10, plain, (![A_7, B_8]: (v1_xboole_0(k2_zfmisc_1(A_7, B_8)) | ~v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.50/2.55  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.50/2.55  tff(c_258, plain, (![A_85]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2')) | ~r2_hidden(A_85, '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_244])).
% 7.50/2.55  tff(c_311, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_258])).
% 7.50/2.55  tff(c_318, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_10, c_311])).
% 7.50/2.55  tff(c_42, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.50/2.55  tff(c_16, plain, (![A_14]: (v2_funct_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.50/2.55  tff(c_65, plain, (![A_14]: (v2_funct_1(k6_partfun1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_16])).
% 7.50/2.55  tff(c_34, plain, (![D_33, A_30, C_32, B_31, E_34, F_35]: (m1_subset_1(k1_partfun1(A_30, B_31, C_32, D_33, E_34, F_35), k1_zfmisc_1(k2_zfmisc_1(A_30, D_33))) | ~m1_subset_1(F_35, k1_zfmisc_1(k2_zfmisc_1(C_32, D_33))) | ~v1_funct_1(F_35) | ~m1_subset_1(E_34, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_1(E_34))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.50/2.55  tff(c_40, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.50/2.55  tff(c_52, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.50/2.55  tff(c_2014, plain, (![D_197, C_198, A_199, B_200]: (D_197=C_198 | ~r2_relset_1(A_199, B_200, C_198, D_197) | ~m1_subset_1(D_197, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.50/2.55  tff(c_2024, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_52, c_2014])).
% 7.50/2.55  tff(c_2043, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2024])).
% 7.50/2.55  tff(c_2056, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2043])).
% 7.50/2.55  tff(c_3512, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_2056])).
% 7.50/2.55  tff(c_3516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_58, c_54, c_3512])).
% 7.50/2.55  tff(c_3517, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2043])).
% 7.50/2.55  tff(c_48, plain, (![E_48, D_46, C_45, A_43, B_44]: (k1_xboole_0=C_45 | v2_funct_1(D_46) | ~v2_funct_1(k1_partfun1(A_43, B_44, B_44, C_45, D_46, E_48)) | ~m1_subset_1(E_48, k1_zfmisc_1(k2_zfmisc_1(B_44, C_45))) | ~v1_funct_2(E_48, B_44, C_45) | ~v1_funct_1(E_48) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_funct_2(D_46, A_43, B_44) | ~v1_funct_1(D_46))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.50/2.55  tff(c_5303, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3517, c_48])).
% 7.50/2.55  tff(c_5312, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_54, c_65, c_5303])).
% 7.50/2.55  tff(c_5313, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_78, c_5312])).
% 7.50/2.55  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.50/2.55  tff(c_5356, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5313, c_6])).
% 7.50/2.55  tff(c_5358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_318, c_5356])).
% 7.50/2.55  tff(c_5360, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_258])).
% 7.50/2.55  tff(c_5361, plain, (![A_375]: (~r2_hidden(A_375, '#skF_5'))), inference(splitRight, [status(thm)], [c_258])).
% 7.50/2.55  tff(c_5366, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_5361])).
% 7.50/2.55  tff(c_8, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.50/2.55  tff(c_5472, plain, (![A_381]: (A_381='#skF_5' | ~v1_xboole_0(A_381))), inference(resolution, [status(thm)], [c_5366, c_8])).
% 7.50/2.55  tff(c_5485, plain, (k2_zfmisc_1('#skF_3', '#skF_2')='#skF_5'), inference(resolution, [status(thm)], [c_5360, c_5472])).
% 7.50/2.55  tff(c_5584, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5485, c_54])).
% 7.50/2.55  tff(c_5621, plain, (![D_387, C_388, A_389, B_390]: (D_387=C_388 | ~r2_relset_1(A_389, B_390, C_388, D_387) | ~m1_subset_1(D_387, k1_zfmisc_1(k2_zfmisc_1(A_389, B_390))) | ~m1_subset_1(C_388, k1_zfmisc_1(k2_zfmisc_1(A_389, B_390))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.50/2.55  tff(c_5627, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_52, c_5621])).
% 7.50/2.55  tff(c_5638, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5627])).
% 7.50/2.55  tff(c_6118, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_5638])).
% 7.50/2.55  tff(c_6232, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_6118])).
% 7.50/2.55  tff(c_6236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_58, c_5584, c_5485, c_6232])).
% 7.50/2.55  tff(c_6237, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_5638])).
% 7.50/2.55  tff(c_79, plain, (![B_55, A_56]: (~v1_xboole_0(B_55) | B_55=A_56 | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.50/2.55  tff(c_82, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_6, c_79])).
% 7.50/2.55  tff(c_5378, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_5366, c_82])).
% 7.50/2.55  tff(c_6106, plain, (![E_48, D_46, C_45, A_43, B_44]: (C_45='#skF_5' | v2_funct_1(D_46) | ~v2_funct_1(k1_partfun1(A_43, B_44, B_44, C_45, D_46, E_48)) | ~m1_subset_1(E_48, k1_zfmisc_1(k2_zfmisc_1(B_44, C_45))) | ~v1_funct_2(E_48, B_44, C_45) | ~v1_funct_1(E_48) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_funct_2(D_46, A_43, B_44) | ~v1_funct_1(D_46))), inference(demodulation, [status(thm), theory('equality')], [c_5378, c_48])).
% 7.50/2.55  tff(c_6357, plain, ('#skF_5'='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6237, c_6106])).
% 7.50/2.55  tff(c_6366, plain, ('#skF_5'='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_5584, c_5485, c_65, c_6357])).
% 7.50/2.55  tff(c_6367, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_78, c_6366])).
% 7.50/2.55  tff(c_6399, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6367, c_5366])).
% 7.50/2.55  tff(c_6405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5471, c_6399])).
% 7.50/2.55  tff(c_6408, plain, (![A_508]: (~r2_hidden(A_508, '#skF_4'))), inference(splitRight, [status(thm)], [c_257])).
% 7.50/2.55  tff(c_6413, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_6408])).
% 7.50/2.55  tff(c_6467, plain, (![A_513]: (A_513='#skF_5' | ~v1_xboole_0(A_513))), inference(demodulation, [status(thm), theory('equality')], [c_5378, c_82])).
% 7.50/2.55  tff(c_6488, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_6413, c_6467])).
% 7.50/2.55  tff(c_97, plain, (![A_60, B_61]: (v1_xboole_0(k2_zfmisc_1(A_60, B_61)) | ~v1_xboole_0(B_61))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.50/2.55  tff(c_136, plain, (![A_66, B_67]: (k2_zfmisc_1(A_66, B_67)=k1_xboole_0 | ~v1_xboole_0(B_67))), inference(resolution, [status(thm)], [c_97, c_82])).
% 7.50/2.55  tff(c_145, plain, (![A_66]: (k2_zfmisc_1(A_66, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_136])).
% 7.50/2.55  tff(c_170, plain, (![A_69]: (m1_subset_1(k6_partfun1(A_69), k1_zfmisc_1(k2_zfmisc_1(A_69, A_69))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.50/2.55  tff(c_174, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_145, c_170])).
% 7.50/2.55  tff(c_246, plain, (![A_85]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_85, k6_partfun1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_174, c_244])).
% 7.50/2.55  tff(c_259, plain, (![A_86]: (~r2_hidden(A_86, k6_partfun1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_246])).
% 7.50/2.55  tff(c_264, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_259])).
% 7.50/2.55  tff(c_276, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_264, c_82])).
% 7.50/2.55  tff(c_298, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_276, c_65])).
% 7.50/2.55  tff(c_5383, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5378, c_298])).
% 7.50/2.55  tff(c_6499, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_5383])).
% 7.50/2.55  tff(c_6511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_6499])).
% 7.50/2.55  tff(c_6512, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 7.50/2.55  tff(c_6615, plain, (![C_529, A_530, B_531]: (v1_relat_1(C_529) | ~m1_subset_1(C_529, k1_zfmisc_1(k2_zfmisc_1(A_530, B_531))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.50/2.55  tff(c_6630, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_6615])).
% 7.50/2.55  tff(c_6639, plain, (![C_534, B_535, A_536]: (v5_relat_1(C_534, B_535) | ~m1_subset_1(C_534, k1_zfmisc_1(k2_zfmisc_1(A_536, B_535))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.50/2.55  tff(c_6656, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_6639])).
% 7.50/2.55  tff(c_6830, plain, (![A_554, B_555, C_556]: (k2_relset_1(A_554, B_555, C_556)=k2_relat_1(C_556) | ~m1_subset_1(C_556, k1_zfmisc_1(k2_zfmisc_1(A_554, B_555))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.50/2.55  tff(c_6847, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_6830])).
% 7.50/2.55  tff(c_8048, plain, (![A_638, B_639, C_640, D_641]: (k2_relset_1(A_638, B_639, C_640)=B_639 | ~r2_relset_1(B_639, B_639, k1_partfun1(B_639, A_638, A_638, B_639, D_641, C_640), k6_partfun1(B_639)) | ~m1_subset_1(D_641, k1_zfmisc_1(k2_zfmisc_1(B_639, A_638))) | ~v1_funct_2(D_641, B_639, A_638) | ~v1_funct_1(D_641) | ~m1_subset_1(C_640, k1_zfmisc_1(k2_zfmisc_1(A_638, B_639))) | ~v1_funct_2(C_640, A_638, B_639) | ~v1_funct_1(C_640))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.50/2.55  tff(c_8066, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_8048])).
% 7.50/2.55  tff(c_8070, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_64, c_62, c_60, c_6847, c_8066])).
% 7.50/2.55  tff(c_30, plain, (![B_29]: (v2_funct_2(B_29, k2_relat_1(B_29)) | ~v5_relat_1(B_29, k2_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.50/2.55  tff(c_8075, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8070, c_30])).
% 7.50/2.55  tff(c_8079, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6630, c_6656, c_8070, c_8075])).
% 7.50/2.55  tff(c_8081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6512, c_8079])).
% 7.50/2.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.50/2.55  
% 7.50/2.55  Inference rules
% 7.50/2.55  ----------------------
% 7.50/2.55  #Ref     : 0
% 7.50/2.55  #Sup     : 2008
% 7.50/2.55  #Fact    : 0
% 7.50/2.55  #Define  : 0
% 7.50/2.55  #Split   : 21
% 7.50/2.55  #Chain   : 0
% 7.50/2.55  #Close   : 0
% 7.50/2.55  
% 7.50/2.55  Ordering : KBO
% 7.50/2.55  
% 7.50/2.55  Simplification rules
% 7.50/2.55  ----------------------
% 7.50/2.55  #Subsume      : 253
% 7.50/2.55  #Demod        : 1452
% 7.50/2.55  #Tautology    : 1017
% 7.50/2.55  #SimpNegUnit  : 8
% 7.50/2.55  #BackRed      : 120
% 7.50/2.55  
% 7.50/2.55  #Partial instantiations: 0
% 7.50/2.55  #Strategies tried      : 1
% 7.50/2.55  
% 7.50/2.55  Timing (in seconds)
% 7.50/2.55  ----------------------
% 7.50/2.55  Preprocessing        : 0.38
% 7.50/2.55  Parsing              : 0.21
% 7.50/2.55  CNF conversion       : 0.03
% 7.50/2.55  Main loop            : 1.35
% 7.50/2.55  Inferencing          : 0.43
% 7.50/2.55  Reduction            : 0.48
% 7.50/2.55  Demodulation         : 0.34
% 7.50/2.55  BG Simplification    : 0.05
% 7.50/2.55  Subsumption          : 0.28
% 7.50/2.55  Abstraction          : 0.05
% 7.50/2.55  MUC search           : 0.00
% 7.50/2.55  Cooper               : 0.00
% 7.50/2.55  Total                : 1.77
% 7.50/2.55  Index Insertion      : 0.00
% 7.50/2.55  Index Deletion       : 0.00
% 7.50/2.55  Index Matching       : 0.00
% 7.50/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
