%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:14 EST 2020

% Result     : Theorem 5.33s
% Output     : CNFRefutation 5.46s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 849 expanded)
%              Number of leaves         :   45 ( 303 expanded)
%              Depth                    :   11
%              Number of atoms          :  242 (2265 expanded)
%              Number of equality atoms :   57 ( 304 expanded)
%              Maximal formula depth    :   15 (   3 average)
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

tff(f_161,negated_conjecture,(
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

tff(f_102,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_56,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_100,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_80,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_141,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_54,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_119,axiom,(
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

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_52,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_120,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_44,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_20,plain,(
    ! [A_12] : v2_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_68,plain,(
    ! [A_12] : v2_funct_1(k6_partfun1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_20])).

tff(c_40,plain,(
    ! [E_33,A_29,F_34,D_32,C_31,B_30] :
      ( m1_subset_1(k1_partfun1(A_29,B_30,C_31,D_32,E_33,F_34),k1_zfmisc_1(k2_zfmisc_1(A_29,D_32)))
      | ~ m1_subset_1(F_34,k1_zfmisc_1(k2_zfmisc_1(C_31,D_32)))
      | ~ v1_funct_1(F_34)
      | ~ m1_subset_1(E_33,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_1(E_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    ! [A_26] : m1_subset_1(k6_relat_1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_67,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_34])).

tff(c_54,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_398,plain,(
    ! [D_105,C_106,A_107,B_108] :
      ( D_105 = C_106
      | ~ r2_relset_1(A_107,B_108,C_106,D_105)
      | ~ m1_subset_1(D_105,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_410,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_398])).

tff(c_433,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_410])).

tff(c_870,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_433])).

tff(c_873,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_870])).

tff(c_877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_873])).

tff(c_878,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_899,plain,(
    ! [C_205,A_204,E_203,B_207,D_206] :
      ( k1_xboole_0 = C_205
      | v2_funct_1(D_206)
      | ~ v2_funct_1(k1_partfun1(A_204,B_207,B_207,C_205,D_206,E_203))
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(B_207,C_205)))
      | ~ v1_funct_2(E_203,B_207,C_205)
      | ~ v1_funct_1(E_203)
      | ~ m1_subset_1(D_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_207)))
      | ~ v1_funct_2(D_206,A_204,B_207)
      | ~ v1_funct_1(D_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_901,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_878,c_899])).

tff(c_903,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_56,c_68,c_901])).

tff(c_904,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_903])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_940,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_904,c_6])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_938,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_904,c_904,c_12])).

tff(c_243,plain,(
    ! [C_75,B_76,A_77] :
      ( ~ v1_xboole_0(C_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(C_75))
      | ~ r2_hidden(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_257,plain,(
    ! [A_77] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2'))
      | ~ r2_hidden(A_77,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_243])).

tff(c_266,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_1076,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_266])).

tff(c_1080,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_940,c_1076])).

tff(c_1082,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_1084,plain,(
    ! [A_226] : ~ r2_hidden(A_226,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_1089,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_1084])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1186,plain,(
    ! [A_231] :
      ( A_231 = '#skF_5'
      | ~ v1_xboole_0(A_231) ) ),
    inference(resolution,[status(thm)],[c_1089,c_8])).

tff(c_1193,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1082,c_1186])).

tff(c_127,plain,(
    ! [B_55,A_56] :
      ( ~ v1_xboole_0(B_55)
      | B_55 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_130,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_127])).

tff(c_1095,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1089,c_130])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1635,plain,(
    ! [B_291,A_292] :
      ( B_291 = '#skF_5'
      | A_292 = '#skF_5'
      | k2_zfmisc_1(A_292,B_291) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_1095,c_1095,c_10])).

tff(c_1645,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1193,c_1635])).

tff(c_1650,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1645])).

tff(c_1674,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1650,c_1089])).

tff(c_1109,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_1095,c_12])).

tff(c_1669,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1650,c_1650,c_1109])).

tff(c_256,plain,(
    ! [A_77] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_77,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_243])).

tff(c_265,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_1769,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1669,c_265])).

tff(c_1773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1674,c_1769])).

tff(c_1774,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1645])).

tff(c_1799,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1774,c_1089])).

tff(c_14,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1108,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_5',B_8) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_1095,c_14])).

tff(c_1791,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_2',B_8) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1774,c_1774,c_1108])).

tff(c_1929,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1791,c_265])).

tff(c_1933,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1799,c_1929])).

tff(c_1937,plain,(
    ! [A_321] : ~ r2_hidden(A_321,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_1942,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_1937])).

tff(c_1948,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1942,c_130])).

tff(c_98,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_18,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_104,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_18])).

tff(c_115,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_68])).

tff(c_1959,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1948,c_115])).

tff(c_1967,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_1959])).

tff(c_1968,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2003,plain,(
    ! [C_329,A_330,B_331] :
      ( v1_relat_1(C_329)
      | ~ m1_subset_1(C_329,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2019,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_2003])).

tff(c_2059,plain,(
    ! [C_339,B_340,A_341] :
      ( v5_relat_1(C_339,B_340)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_341,B_340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2077,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_2059])).

tff(c_2147,plain,(
    ! [A_358,B_359,D_360] :
      ( r2_relset_1(A_358,B_359,D_360,D_360)
      | ~ m1_subset_1(D_360,k1_zfmisc_1(k2_zfmisc_1(A_358,B_359))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2158,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_67,c_2147])).

tff(c_2203,plain,(
    ! [A_365,B_366,C_367] :
      ( k2_relset_1(A_365,B_366,C_367) = k2_relat_1(C_367)
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1(A_365,B_366))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2221,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_2203])).

tff(c_2392,plain,(
    ! [C_405,F_403,E_404,D_400,A_402,B_401] :
      ( m1_subset_1(k1_partfun1(A_402,B_401,C_405,D_400,E_404,F_403),k1_zfmisc_1(k2_zfmisc_1(A_402,D_400)))
      | ~ m1_subset_1(F_403,k1_zfmisc_1(k2_zfmisc_1(C_405,D_400)))
      | ~ v1_funct_1(F_403)
      | ~ m1_subset_1(E_404,k1_zfmisc_1(k2_zfmisc_1(A_402,B_401)))
      | ~ v1_funct_1(E_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2252,plain,(
    ! [D_370,C_371,A_372,B_373] :
      ( D_370 = C_371
      | ~ r2_relset_1(A_372,B_373,C_371,D_370)
      | ~ m1_subset_1(D_370,k1_zfmisc_1(k2_zfmisc_1(A_372,B_373)))
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(A_372,B_373))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2262,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_2252])).

tff(c_2281,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_2262])).

tff(c_2298,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2281])).

tff(c_2398,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2392,c_2298])).

tff(c_2427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_2398])).

tff(c_2428,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2281])).

tff(c_2751,plain,(
    ! [A_490,B_491,C_492,D_493] :
      ( k2_relset_1(A_490,B_491,C_492) = B_491
      | ~ r2_relset_1(B_491,B_491,k1_partfun1(B_491,A_490,A_490,B_491,D_493,C_492),k6_partfun1(B_491))
      | ~ m1_subset_1(D_493,k1_zfmisc_1(k2_zfmisc_1(B_491,A_490)))
      | ~ v1_funct_2(D_493,B_491,A_490)
      | ~ v1_funct_1(D_493)
      | ~ m1_subset_1(C_492,k1_zfmisc_1(k2_zfmisc_1(A_490,B_491)))
      | ~ v1_funct_2(C_492,A_490,B_491)
      | ~ v1_funct_1(C_492) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2754,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2428,c_2751])).

tff(c_2759,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_66,c_64,c_62,c_2158,c_2221,c_2754])).

tff(c_36,plain,(
    ! [B_28] :
      ( v2_funct_2(B_28,k2_relat_1(B_28))
      | ~ v5_relat_1(B_28,k2_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2765,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2759,c_36])).

tff(c_2769,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2019,c_2077,c_2759,c_2765])).

tff(c_2771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1968,c_2769])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:24:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.33/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.05  
% 5.33/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.05  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.33/2.05  
% 5.33/2.05  %Foreground sorts:
% 5.33/2.05  
% 5.33/2.05  
% 5.33/2.05  %Background operators:
% 5.33/2.05  
% 5.33/2.05  
% 5.33/2.05  %Foreground operators:
% 5.33/2.05  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.33/2.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.33/2.05  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.33/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.33/2.05  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.33/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.33/2.05  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.33/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.33/2.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.33/2.05  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.33/2.05  tff('#skF_5', type, '#skF_5': $i).
% 5.33/2.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.33/2.05  tff('#skF_2', type, '#skF_2': $i).
% 5.33/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.33/2.05  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.33/2.05  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.33/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.33/2.05  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.33/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.33/2.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.33/2.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.33/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.33/2.05  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.33/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.33/2.05  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.33/2.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.33/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.33/2.05  
% 5.46/2.07  tff(f_161, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 5.46/2.07  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.46/2.07  tff(f_102, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.46/2.07  tff(f_56, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 5.46/2.07  tff(f_100, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.46/2.07  tff(f_80, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.46/2.07  tff(f_78, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.46/2.07  tff(f_141, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 5.46/2.07  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.46/2.07  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.46/2.07  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.46/2.07  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 5.46/2.07  tff(f_54, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 5.46/2.07  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.46/2.07  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.46/2.07  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.46/2.07  tff(f_119, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 5.46/2.07  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.46/2.07  tff(c_52, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.46/2.07  tff(c_120, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 5.46/2.07  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.46/2.07  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.46/2.07  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.46/2.07  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.46/2.07  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.46/2.07  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.46/2.07  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.46/2.07  tff(c_44, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.46/2.07  tff(c_20, plain, (![A_12]: (v2_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.46/2.07  tff(c_68, plain, (![A_12]: (v2_funct_1(k6_partfun1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_20])).
% 5.46/2.07  tff(c_40, plain, (![E_33, A_29, F_34, D_32, C_31, B_30]: (m1_subset_1(k1_partfun1(A_29, B_30, C_31, D_32, E_33, F_34), k1_zfmisc_1(k2_zfmisc_1(A_29, D_32))) | ~m1_subset_1(F_34, k1_zfmisc_1(k2_zfmisc_1(C_31, D_32))) | ~v1_funct_1(F_34) | ~m1_subset_1(E_33, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_1(E_33))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.46/2.07  tff(c_34, plain, (![A_26]: (m1_subset_1(k6_relat_1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.46/2.07  tff(c_67, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_34])).
% 5.46/2.07  tff(c_54, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.46/2.07  tff(c_398, plain, (![D_105, C_106, A_107, B_108]: (D_105=C_106 | ~r2_relset_1(A_107, B_108, C_106, D_105) | ~m1_subset_1(D_105, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.46/2.07  tff(c_410, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_398])).
% 5.46/2.07  tff(c_433, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_410])).
% 5.46/2.07  tff(c_870, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_433])).
% 5.46/2.07  tff(c_873, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_870])).
% 5.46/2.07  tff(c_877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_873])).
% 5.46/2.07  tff(c_878, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_433])).
% 5.46/2.07  tff(c_899, plain, (![C_205, A_204, E_203, B_207, D_206]: (k1_xboole_0=C_205 | v2_funct_1(D_206) | ~v2_funct_1(k1_partfun1(A_204, B_207, B_207, C_205, D_206, E_203)) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(B_207, C_205))) | ~v1_funct_2(E_203, B_207, C_205) | ~v1_funct_1(E_203) | ~m1_subset_1(D_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_207))) | ~v1_funct_2(D_206, A_204, B_207) | ~v1_funct_1(D_206))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.46/2.07  tff(c_901, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_878, c_899])).
% 5.46/2.07  tff(c_903, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_56, c_68, c_901])).
% 5.46/2.07  tff(c_904, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_120, c_903])).
% 5.46/2.07  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.46/2.07  tff(c_940, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_904, c_6])).
% 5.46/2.07  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.46/2.07  tff(c_938, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_904, c_904, c_12])).
% 5.46/2.07  tff(c_243, plain, (![C_75, B_76, A_77]: (~v1_xboole_0(C_75) | ~m1_subset_1(B_76, k1_zfmisc_1(C_75)) | ~r2_hidden(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.46/2.07  tff(c_257, plain, (![A_77]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2')) | ~r2_hidden(A_77, '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_243])).
% 5.46/2.07  tff(c_266, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_257])).
% 5.46/2.07  tff(c_1076, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_938, c_266])).
% 5.46/2.07  tff(c_1080, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_940, c_1076])).
% 5.46/2.07  tff(c_1082, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_257])).
% 5.46/2.07  tff(c_1084, plain, (![A_226]: (~r2_hidden(A_226, '#skF_5'))), inference(splitRight, [status(thm)], [c_257])).
% 5.46/2.07  tff(c_1089, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_1084])).
% 5.46/2.07  tff(c_8, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.46/2.07  tff(c_1186, plain, (![A_231]: (A_231='#skF_5' | ~v1_xboole_0(A_231))), inference(resolution, [status(thm)], [c_1089, c_8])).
% 5.46/2.07  tff(c_1193, plain, (k2_zfmisc_1('#skF_3', '#skF_2')='#skF_5'), inference(resolution, [status(thm)], [c_1082, c_1186])).
% 5.46/2.07  tff(c_127, plain, (![B_55, A_56]: (~v1_xboole_0(B_55) | B_55=A_56 | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.46/2.07  tff(c_130, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_6, c_127])).
% 5.46/2.07  tff(c_1095, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1089, c_130])).
% 5.46/2.07  tff(c_10, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.46/2.07  tff(c_1635, plain, (![B_291, A_292]: (B_291='#skF_5' | A_292='#skF_5' | k2_zfmisc_1(A_292, B_291)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1095, c_1095, c_1095, c_10])).
% 5.46/2.07  tff(c_1645, plain, ('#skF_5'='#skF_2' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1193, c_1635])).
% 5.46/2.07  tff(c_1650, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_1645])).
% 5.46/2.07  tff(c_1674, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1650, c_1089])).
% 5.46/2.07  tff(c_1109, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1095, c_1095, c_12])).
% 5.46/2.07  tff(c_1669, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1650, c_1650, c_1109])).
% 5.46/2.07  tff(c_256, plain, (![A_77]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_77, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_243])).
% 5.46/2.07  tff(c_265, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_256])).
% 5.46/2.07  tff(c_1769, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1669, c_265])).
% 5.46/2.07  tff(c_1773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1674, c_1769])).
% 5.46/2.07  tff(c_1774, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_1645])).
% 5.46/2.07  tff(c_1799, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1774, c_1089])).
% 5.46/2.07  tff(c_14, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.46/2.07  tff(c_1108, plain, (![B_8]: (k2_zfmisc_1('#skF_5', B_8)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1095, c_1095, c_14])).
% 5.46/2.07  tff(c_1791, plain, (![B_8]: (k2_zfmisc_1('#skF_2', B_8)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1774, c_1774, c_1108])).
% 5.46/2.07  tff(c_1929, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1791, c_265])).
% 5.46/2.07  tff(c_1933, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1799, c_1929])).
% 5.46/2.07  tff(c_1937, plain, (![A_321]: (~r2_hidden(A_321, '#skF_4'))), inference(splitRight, [status(thm)], [c_256])).
% 5.46/2.07  tff(c_1942, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_1937])).
% 5.46/2.07  tff(c_1948, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1942, c_130])).
% 5.46/2.07  tff(c_98, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.46/2.07  tff(c_18, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.46/2.07  tff(c_104, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_98, c_18])).
% 5.46/2.07  tff(c_115, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_104, c_68])).
% 5.46/2.07  tff(c_1959, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1948, c_115])).
% 5.46/2.07  tff(c_1967, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_1959])).
% 5.46/2.07  tff(c_1968, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 5.46/2.07  tff(c_2003, plain, (![C_329, A_330, B_331]: (v1_relat_1(C_329) | ~m1_subset_1(C_329, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.46/2.07  tff(c_2019, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_2003])).
% 5.46/2.07  tff(c_2059, plain, (![C_339, B_340, A_341]: (v5_relat_1(C_339, B_340) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_341, B_340))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.46/2.07  tff(c_2077, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_2059])).
% 5.46/2.07  tff(c_2147, plain, (![A_358, B_359, D_360]: (r2_relset_1(A_358, B_359, D_360, D_360) | ~m1_subset_1(D_360, k1_zfmisc_1(k2_zfmisc_1(A_358, B_359))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.46/2.07  tff(c_2158, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_67, c_2147])).
% 5.46/2.07  tff(c_2203, plain, (![A_365, B_366, C_367]: (k2_relset_1(A_365, B_366, C_367)=k2_relat_1(C_367) | ~m1_subset_1(C_367, k1_zfmisc_1(k2_zfmisc_1(A_365, B_366))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.46/2.07  tff(c_2221, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_2203])).
% 5.46/2.07  tff(c_2392, plain, (![C_405, F_403, E_404, D_400, A_402, B_401]: (m1_subset_1(k1_partfun1(A_402, B_401, C_405, D_400, E_404, F_403), k1_zfmisc_1(k2_zfmisc_1(A_402, D_400))) | ~m1_subset_1(F_403, k1_zfmisc_1(k2_zfmisc_1(C_405, D_400))) | ~v1_funct_1(F_403) | ~m1_subset_1(E_404, k1_zfmisc_1(k2_zfmisc_1(A_402, B_401))) | ~v1_funct_1(E_404))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.46/2.07  tff(c_2252, plain, (![D_370, C_371, A_372, B_373]: (D_370=C_371 | ~r2_relset_1(A_372, B_373, C_371, D_370) | ~m1_subset_1(D_370, k1_zfmisc_1(k2_zfmisc_1(A_372, B_373))) | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(A_372, B_373))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.46/2.07  tff(c_2262, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_2252])).
% 5.46/2.07  tff(c_2281, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_2262])).
% 5.46/2.07  tff(c_2298, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2281])).
% 5.46/2.07  tff(c_2398, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_2392, c_2298])).
% 5.46/2.07  tff(c_2427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_2398])).
% 5.46/2.07  tff(c_2428, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2281])).
% 5.46/2.07  tff(c_2751, plain, (![A_490, B_491, C_492, D_493]: (k2_relset_1(A_490, B_491, C_492)=B_491 | ~r2_relset_1(B_491, B_491, k1_partfun1(B_491, A_490, A_490, B_491, D_493, C_492), k6_partfun1(B_491)) | ~m1_subset_1(D_493, k1_zfmisc_1(k2_zfmisc_1(B_491, A_490))) | ~v1_funct_2(D_493, B_491, A_490) | ~v1_funct_1(D_493) | ~m1_subset_1(C_492, k1_zfmisc_1(k2_zfmisc_1(A_490, B_491))) | ~v1_funct_2(C_492, A_490, B_491) | ~v1_funct_1(C_492))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.46/2.07  tff(c_2754, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2428, c_2751])).
% 5.46/2.07  tff(c_2759, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_66, c_64, c_62, c_2158, c_2221, c_2754])).
% 5.46/2.07  tff(c_36, plain, (![B_28]: (v2_funct_2(B_28, k2_relat_1(B_28)) | ~v5_relat_1(B_28, k2_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.46/2.07  tff(c_2765, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2759, c_36])).
% 5.46/2.07  tff(c_2769, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2019, c_2077, c_2759, c_2765])).
% 5.46/2.07  tff(c_2771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1968, c_2769])).
% 5.46/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.46/2.07  
% 5.46/2.07  Inference rules
% 5.46/2.07  ----------------------
% 5.46/2.07  #Ref     : 0
% 5.46/2.07  #Sup     : 603
% 5.46/2.07  #Fact    : 0
% 5.46/2.07  #Define  : 0
% 5.46/2.07  #Split   : 20
% 5.46/2.07  #Chain   : 0
% 5.46/2.07  #Close   : 0
% 5.46/2.07  
% 5.46/2.07  Ordering : KBO
% 5.46/2.07  
% 5.46/2.07  Simplification rules
% 5.46/2.07  ----------------------
% 5.46/2.07  #Subsume      : 72
% 5.46/2.08  #Demod        : 662
% 5.46/2.08  #Tautology    : 222
% 5.46/2.08  #SimpNegUnit  : 5
% 5.46/2.08  #BackRed      : 179
% 5.46/2.08  
% 5.46/2.08  #Partial instantiations: 0
% 5.46/2.08  #Strategies tried      : 1
% 5.46/2.08  
% 5.46/2.08  Timing (in seconds)
% 5.46/2.08  ----------------------
% 5.46/2.08  Preprocessing        : 0.39
% 5.46/2.08  Parsing              : 0.22
% 5.46/2.08  CNF conversion       : 0.03
% 5.46/2.08  Main loop            : 0.81
% 5.46/2.08  Inferencing          : 0.28
% 5.46/2.08  Reduction            : 0.29
% 5.46/2.08  Demodulation         : 0.21
% 5.46/2.08  BG Simplification    : 0.03
% 5.46/2.08  Subsumption          : 0.13
% 5.46/2.08  Abstraction          : 0.03
% 5.46/2.08  MUC search           : 0.00
% 5.46/2.08  Cooper               : 0.00
% 5.46/2.08  Total                : 1.25
% 5.46/2.08  Index Insertion      : 0.00
% 5.46/2.08  Index Deletion       : 0.00
% 5.46/2.08  Index Matching       : 0.00
% 5.46/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
