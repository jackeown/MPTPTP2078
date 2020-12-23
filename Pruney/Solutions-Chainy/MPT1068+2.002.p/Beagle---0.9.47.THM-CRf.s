%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:41 EST 2020

% Result     : Theorem 11.66s
% Output     : CNFRefutation 11.66s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 480 expanded)
%              Number of leaves         :   41 ( 183 expanded)
%              Depth                    :   13
%              Number of atoms          :  355 (1642 expanded)
%              Number of equality atoms :   86 ( 331 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_170,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_145,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_117,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_62,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_103,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_115,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_103])).

tff(c_66,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_160,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_2'(A_80,B_81),A_80)
      | r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_170,plain,(
    ! [A_80,B_81] :
      ( ~ v1_xboole_0(A_80)
      | r1_tarski(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_160,c_2])).

tff(c_89,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_100,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_89])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_217,plain,(
    ! [C_90,B_91,A_92] :
      ( r2_hidden(C_90,B_91)
      | ~ r2_hidden(C_90,A_92)
      | ~ r1_tarski(A_92,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3972,plain,(
    ! [A_493,B_494,B_495] :
      ( r2_hidden('#skF_2'(A_493,B_494),B_495)
      | ~ r1_tarski(A_493,B_495)
      | r1_tarski(A_493,B_494) ) ),
    inference(resolution,[status(thm)],[c_10,c_217])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8308,plain,(
    ! [A_881,B_882,B_883,B_884] :
      ( r2_hidden('#skF_2'(A_881,B_882),B_883)
      | ~ r1_tarski(B_884,B_883)
      | ~ r1_tarski(A_881,B_884)
      | r1_tarski(A_881,B_882) ) ),
    inference(resolution,[status(thm)],[c_3972,c_6])).

tff(c_8410,plain,(
    ! [A_891,B_892] :
      ( r2_hidden('#skF_2'(A_891,B_892),k2_zfmisc_1('#skF_5','#skF_3'))
      | ~ r1_tarski(A_891,'#skF_7')
      | r1_tarski(A_891,B_892) ) ),
    inference(resolution,[status(thm)],[c_100,c_8308])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8435,plain,(
    ! [A_894] :
      ( ~ r1_tarski(A_894,'#skF_7')
      | r1_tarski(A_894,k2_zfmisc_1('#skF_5','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8410,c_8])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_225,plain,(
    ! [A_12,B_91,B_13] :
      ( r2_hidden(A_12,B_91)
      | ~ r1_tarski(B_13,B_91)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_217])).

tff(c_8587,plain,(
    ! [A_903,A_904] :
      ( r2_hidden(A_903,k2_zfmisc_1('#skF_5','#skF_3'))
      | v1_xboole_0(A_904)
      | ~ m1_subset_1(A_903,A_904)
      | ~ r1_tarski(A_904,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_8435,c_225])).

tff(c_8599,plain,
    ( r2_hidden('#skF_8',k2_zfmisc_1('#skF_5','#skF_3'))
    | v1_xboole_0('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_8587])).

tff(c_8600,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_8599])).

tff(c_8604,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_170,c_8600])).

tff(c_70,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_260,plain,(
    ! [A_97,B_98,C_99] :
      ( k1_relset_1(A_97,B_98,C_99) = k1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_273,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_260])).

tff(c_8251,plain,(
    ! [B_875,A_876,C_877] :
      ( k1_xboole_0 = B_875
      | k1_relset_1(A_876,B_875,C_877) = A_876
      | ~ v1_funct_2(C_877,A_876,B_875)
      | ~ m1_subset_1(C_877,k1_zfmisc_1(k2_zfmisc_1(A_876,B_875))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_8261,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_8251])).

tff(c_8267,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_273,c_8261])).

tff(c_8268,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8267])).

tff(c_116,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_103])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_8625,plain,(
    ! [B_907,C_908,A_909] :
      ( k1_funct_1(k5_relat_1(B_907,C_908),A_909) = k1_funct_1(C_908,k1_funct_1(B_907,A_909))
      | ~ r2_hidden(A_909,k1_relat_1(B_907))
      | ~ v1_funct_1(C_908)
      | ~ v1_relat_1(C_908)
      | ~ v1_funct_1(B_907)
      | ~ v1_relat_1(B_907) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_11937,plain,(
    ! [B_1212,C_1213,A_1214] :
      ( k1_funct_1(k5_relat_1(B_1212,C_1213),A_1214) = k1_funct_1(C_1213,k1_funct_1(B_1212,A_1214))
      | ~ v1_funct_1(C_1213)
      | ~ v1_relat_1(C_1213)
      | ~ v1_funct_1(B_1212)
      | ~ v1_relat_1(B_1212)
      | v1_xboole_0(k1_relat_1(B_1212))
      | ~ m1_subset_1(A_1214,k1_relat_1(B_1212)) ) ),
    inference(resolution,[status(thm)],[c_20,c_8625])).

tff(c_11939,plain,(
    ! [C_1213,A_1214] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_1213),A_1214) = k1_funct_1(C_1213,k1_funct_1('#skF_6',A_1214))
      | ~ v1_funct_1(C_1213)
      | ~ v1_relat_1(C_1213)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | v1_xboole_0(k1_relat_1('#skF_6'))
      | ~ m1_subset_1(A_1214,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8268,c_11937])).

tff(c_11941,plain,(
    ! [C_1213,A_1214] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_1213),A_1214) = k1_funct_1(C_1213,k1_funct_1('#skF_6',A_1214))
      | ~ v1_funct_1(C_1213)
      | ~ v1_relat_1(C_1213)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_1214,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8268,c_116,c_72,c_11939])).

tff(c_11942,plain,(
    ! [C_1213,A_1214] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_1213),A_1214) = k1_funct_1(C_1213,k1_funct_1('#skF_6',A_1214))
      | ~ v1_funct_1(C_1213)
      | ~ v1_relat_1(C_1213)
      | ~ m1_subset_1(A_1214,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_8604,c_11941])).

tff(c_8692,plain,(
    ! [E_912,D_914,F_915,B_917,A_913,C_916] :
      ( k1_partfun1(A_913,B_917,C_916,D_914,E_912,F_915) = k5_relat_1(E_912,F_915)
      | ~ m1_subset_1(F_915,k1_zfmisc_1(k2_zfmisc_1(C_916,D_914)))
      | ~ v1_funct_1(F_915)
      | ~ m1_subset_1(E_912,k1_zfmisc_1(k2_zfmisc_1(A_913,B_917)))
      | ~ v1_funct_1(E_912) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_8697,plain,(
    ! [A_913,B_917,E_912] :
      ( k1_partfun1(A_913,B_917,'#skF_5','#skF_3',E_912,'#skF_7') = k5_relat_1(E_912,'#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_912,k1_zfmisc_1(k2_zfmisc_1(A_913,B_917)))
      | ~ v1_funct_1(E_912) ) ),
    inference(resolution,[status(thm)],[c_64,c_8692])).

tff(c_11702,plain,(
    ! [A_1195,B_1196,E_1197] :
      ( k1_partfun1(A_1195,B_1196,'#skF_5','#skF_3',E_1197,'#skF_7') = k5_relat_1(E_1197,'#skF_7')
      | ~ m1_subset_1(E_1197,k1_zfmisc_1(k2_zfmisc_1(A_1195,B_1196)))
      | ~ v1_funct_1(E_1197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8697])).

tff(c_11712,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_11702])).

tff(c_11719,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_11712])).

tff(c_272,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_260])).

tff(c_60,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_279,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_60])).

tff(c_101,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_68,c_89])).

tff(c_8324,plain,(
    ! [A_885,B_886] :
      ( r2_hidden('#skF_2'(A_885,B_886),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_885,'#skF_6')
      | r1_tarski(A_885,B_886) ) ),
    inference(resolution,[status(thm)],[c_101,c_8308])).

tff(c_8335,plain,(
    ! [A_885] :
      ( ~ r1_tarski(A_885,'#skF_6')
      | r1_tarski(A_885,k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_8324,c_8])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8865,plain,(
    ! [B_935,A_936,A_937] :
      ( k1_xboole_0 = B_935
      | k1_relset_1(A_936,B_935,A_937) = A_936
      | ~ v1_funct_2(A_937,A_936,B_935)
      | ~ r1_tarski(A_937,k2_zfmisc_1(A_936,B_935)) ) ),
    inference(resolution,[status(thm)],[c_24,c_8251])).

tff(c_8887,plain,(
    ! [A_885] :
      ( k1_xboole_0 = '#skF_5'
      | k1_relset_1('#skF_4','#skF_5',A_885) = '#skF_4'
      | ~ v1_funct_2(A_885,'#skF_4','#skF_5')
      | ~ r1_tarski(A_885,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_8335,c_8865])).

tff(c_11265,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_8887])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_11324,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11265,c_12])).

tff(c_11327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_11324])).

tff(c_11329,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_8887])).

tff(c_8791,plain,(
    ! [C_927,A_926,B_924,D_923,E_925] :
      ( k1_partfun1(A_926,B_924,B_924,C_927,D_923,E_925) = k8_funct_2(A_926,B_924,C_927,D_923,E_925)
      | k1_xboole_0 = B_924
      | ~ r1_tarski(k2_relset_1(A_926,B_924,D_923),k1_relset_1(B_924,C_927,E_925))
      | ~ m1_subset_1(E_925,k1_zfmisc_1(k2_zfmisc_1(B_924,C_927)))
      | ~ v1_funct_1(E_925)
      | ~ m1_subset_1(D_923,k1_zfmisc_1(k2_zfmisc_1(A_926,B_924)))
      | ~ v1_funct_2(D_923,A_926,B_924)
      | ~ v1_funct_1(D_923) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8803,plain,(
    ! [A_926,D_923] :
      ( k1_partfun1(A_926,'#skF_5','#skF_5','#skF_3',D_923,'#skF_7') = k8_funct_2(A_926,'#skF_5','#skF_3',D_923,'#skF_7')
      | k1_xboole_0 = '#skF_5'
      | ~ r1_tarski(k2_relset_1(A_926,'#skF_5',D_923),k1_relat_1('#skF_7'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_923,k1_zfmisc_1(k2_zfmisc_1(A_926,'#skF_5')))
      | ~ v1_funct_2(D_923,A_926,'#skF_5')
      | ~ v1_funct_1(D_923) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_8791])).

tff(c_8813,plain,(
    ! [A_926,D_923] :
      ( k1_partfun1(A_926,'#skF_5','#skF_5','#skF_3',D_923,'#skF_7') = k8_funct_2(A_926,'#skF_5','#skF_3',D_923,'#skF_7')
      | k1_xboole_0 = '#skF_5'
      | ~ r1_tarski(k2_relset_1(A_926,'#skF_5',D_923),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(D_923,k1_zfmisc_1(k2_zfmisc_1(A_926,'#skF_5')))
      | ~ v1_funct_2(D_923,A_926,'#skF_5')
      | ~ v1_funct_1(D_923) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_8803])).

tff(c_14457,plain,(
    ! [A_1405,D_1406] :
      ( k1_partfun1(A_1405,'#skF_5','#skF_5','#skF_3',D_1406,'#skF_7') = k8_funct_2(A_1405,'#skF_5','#skF_3',D_1406,'#skF_7')
      | ~ r1_tarski(k2_relset_1(A_1405,'#skF_5',D_1406),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(D_1406,k1_zfmisc_1(k2_zfmisc_1(A_1405,'#skF_5')))
      | ~ v1_funct_2(D_1406,A_1405,'#skF_5')
      | ~ v1_funct_1(D_1406) ) ),
    inference(negUnitSimplification,[status(thm)],[c_11329,c_8813])).

tff(c_14469,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_279,c_14457])).

tff(c_14475,plain,(
    k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_11719,c_14469])).

tff(c_56,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_14508,plain,(
    k1_funct_1(k5_relat_1('#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14475,c_56])).

tff(c_14515,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11942,c_14508])).

tff(c_14522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_115,c_66,c_14515])).

tff(c_14524,plain,(
    r1_tarski('#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_8599])).

tff(c_14552,plain,(
    ! [A_12] :
      ( r2_hidden(A_12,'#skF_7')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_12,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14524,c_225])).

tff(c_14632,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_14552])).

tff(c_171,plain,(
    ! [A_82,B_83] :
      ( ~ v1_xboole_0(A_82)
      | r1_tarski(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_160,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_185,plain,(
    ! [B_85,A_86] :
      ( B_85 = A_86
      | ~ r1_tarski(B_85,A_86)
      | ~ v1_xboole_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_171,c_14])).

tff(c_207,plain,(
    ! [B_87,A_88] :
      ( B_87 = A_88
      | ~ v1_xboole_0(B_87)
      | ~ v1_xboole_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_170,c_185])).

tff(c_210,plain,(
    ! [A_88] :
      ( k1_xboole_0 = A_88
      | ~ v1_xboole_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_12,c_207])).

tff(c_14637,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14632,c_210])).

tff(c_14650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_14637])).

tff(c_14652,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_14552])).

tff(c_14556,plain,(
    ! [B_1408,C_1409,A_1410] :
      ( k1_funct_1(k5_relat_1(B_1408,C_1409),A_1410) = k1_funct_1(C_1409,k1_funct_1(B_1408,A_1410))
      | ~ r2_hidden(A_1410,k1_relat_1(B_1408))
      | ~ v1_funct_1(C_1409)
      | ~ v1_relat_1(C_1409)
      | ~ v1_funct_1(B_1408)
      | ~ v1_relat_1(B_1408) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_15583,plain,(
    ! [B_1503,C_1504,A_1505] :
      ( k1_funct_1(k5_relat_1(B_1503,C_1504),A_1505) = k1_funct_1(C_1504,k1_funct_1(B_1503,A_1505))
      | ~ v1_funct_1(C_1504)
      | ~ v1_relat_1(C_1504)
      | ~ v1_funct_1(B_1503)
      | ~ v1_relat_1(B_1503)
      | v1_xboole_0(k1_relat_1(B_1503))
      | ~ m1_subset_1(A_1505,k1_relat_1(B_1503)) ) ),
    inference(resolution,[status(thm)],[c_20,c_14556])).

tff(c_15585,plain,(
    ! [C_1504,A_1505] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_1504),A_1505) = k1_funct_1(C_1504,k1_funct_1('#skF_6',A_1505))
      | ~ v1_funct_1(C_1504)
      | ~ v1_relat_1(C_1504)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | v1_xboole_0(k1_relat_1('#skF_6'))
      | ~ m1_subset_1(A_1505,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8268,c_15583])).

tff(c_15587,plain,(
    ! [C_1504,A_1505] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_1504),A_1505) = k1_funct_1(C_1504,k1_funct_1('#skF_6',A_1505))
      | ~ v1_funct_1(C_1504)
      | ~ v1_relat_1(C_1504)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_1505,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8268,c_116,c_72,c_15585])).

tff(c_15588,plain,(
    ! [C_1504,A_1505] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_1504),A_1505) = k1_funct_1(C_1504,k1_funct_1('#skF_6',A_1505))
      | ~ v1_funct_1(C_1504)
      | ~ v1_relat_1(C_1504)
      | ~ m1_subset_1(A_1505,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_14652,c_15587])).

tff(c_14617,plain,(
    ! [A_1412,C_1415,D_1413,B_1416,F_1414,E_1411] :
      ( k1_partfun1(A_1412,B_1416,C_1415,D_1413,E_1411,F_1414) = k5_relat_1(E_1411,F_1414)
      | ~ m1_subset_1(F_1414,k1_zfmisc_1(k2_zfmisc_1(C_1415,D_1413)))
      | ~ v1_funct_1(F_1414)
      | ~ m1_subset_1(E_1411,k1_zfmisc_1(k2_zfmisc_1(A_1412,B_1416)))
      | ~ v1_funct_1(E_1411) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_14622,plain,(
    ! [A_1412,B_1416,E_1411] :
      ( k1_partfun1(A_1412,B_1416,'#skF_5','#skF_3',E_1411,'#skF_7') = k5_relat_1(E_1411,'#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1411,k1_zfmisc_1(k2_zfmisc_1(A_1412,B_1416)))
      | ~ v1_funct_1(E_1411) ) ),
    inference(resolution,[status(thm)],[c_64,c_14617])).

tff(c_15209,plain,(
    ! [A_1460,B_1461,E_1462] :
      ( k1_partfun1(A_1460,B_1461,'#skF_5','#skF_3',E_1462,'#skF_7') = k5_relat_1(E_1462,'#skF_7')
      | ~ m1_subset_1(E_1462,k1_zfmisc_1(k2_zfmisc_1(A_1460,B_1461)))
      | ~ v1_funct_1(E_1462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_14622])).

tff(c_15219,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_15209])).

tff(c_15226,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_15219])).

tff(c_8337,plain,(
    ! [B_887,C_888,A_889] :
      ( k1_xboole_0 = B_887
      | v1_funct_2(C_888,A_889,B_887)
      | k1_relset_1(A_889,B_887,C_888) != A_889
      | ~ m1_subset_1(C_888,k1_zfmisc_1(k2_zfmisc_1(A_889,B_887))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_14802,plain,(
    ! [B_1433,A_1434,A_1435] :
      ( k1_xboole_0 = B_1433
      | v1_funct_2(A_1434,A_1435,B_1433)
      | k1_relset_1(A_1435,B_1433,A_1434) != A_1435
      | ~ r1_tarski(A_1434,k2_zfmisc_1(A_1435,B_1433)) ) ),
    inference(resolution,[status(thm)],[c_24,c_8337])).

tff(c_14824,plain,(
    ! [A_885] :
      ( k1_xboole_0 = '#skF_5'
      | v1_funct_2(A_885,'#skF_4','#skF_5')
      | k1_relset_1('#skF_4','#skF_5',A_885) != '#skF_4'
      | ~ r1_tarski(A_885,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_8335,c_14802])).

tff(c_16564,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_14824])).

tff(c_16616,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16564,c_12])).

tff(c_16619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_16616])).

tff(c_16621,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_14824])).

tff(c_14695,plain,(
    ! [B_1421,A_1423,C_1424,D_1420,E_1422] :
      ( k1_partfun1(A_1423,B_1421,B_1421,C_1424,D_1420,E_1422) = k8_funct_2(A_1423,B_1421,C_1424,D_1420,E_1422)
      | k1_xboole_0 = B_1421
      | ~ r1_tarski(k2_relset_1(A_1423,B_1421,D_1420),k1_relset_1(B_1421,C_1424,E_1422))
      | ~ m1_subset_1(E_1422,k1_zfmisc_1(k2_zfmisc_1(B_1421,C_1424)))
      | ~ v1_funct_1(E_1422)
      | ~ m1_subset_1(D_1420,k1_zfmisc_1(k2_zfmisc_1(A_1423,B_1421)))
      | ~ v1_funct_2(D_1420,A_1423,B_1421)
      | ~ v1_funct_1(D_1420) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_14710,plain,(
    ! [A_1423,D_1420] :
      ( k1_partfun1(A_1423,'#skF_5','#skF_5','#skF_3',D_1420,'#skF_7') = k8_funct_2(A_1423,'#skF_5','#skF_3',D_1420,'#skF_7')
      | k1_xboole_0 = '#skF_5'
      | ~ r1_tarski(k2_relset_1(A_1423,'#skF_5',D_1420),k1_relat_1('#skF_7'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_1420,k1_zfmisc_1(k2_zfmisc_1(A_1423,'#skF_5')))
      | ~ v1_funct_2(D_1420,A_1423,'#skF_5')
      | ~ v1_funct_1(D_1420) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_14695])).

tff(c_14720,plain,(
    ! [A_1423,D_1420] :
      ( k1_partfun1(A_1423,'#skF_5','#skF_5','#skF_3',D_1420,'#skF_7') = k8_funct_2(A_1423,'#skF_5','#skF_3',D_1420,'#skF_7')
      | k1_xboole_0 = '#skF_5'
      | ~ r1_tarski(k2_relset_1(A_1423,'#skF_5',D_1420),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(D_1420,k1_zfmisc_1(k2_zfmisc_1(A_1423,'#skF_5')))
      | ~ v1_funct_2(D_1420,A_1423,'#skF_5')
      | ~ v1_funct_1(D_1420) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_14710])).

tff(c_18168,plain,(
    ! [A_1653,D_1654] :
      ( k1_partfun1(A_1653,'#skF_5','#skF_5','#skF_3',D_1654,'#skF_7') = k8_funct_2(A_1653,'#skF_5','#skF_3',D_1654,'#skF_7')
      | ~ r1_tarski(k2_relset_1(A_1653,'#skF_5',D_1654),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(D_1654,k1_zfmisc_1(k2_zfmisc_1(A_1653,'#skF_5')))
      | ~ v1_funct_2(D_1654,A_1653,'#skF_5')
      | ~ v1_funct_1(D_1654) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16621,c_14720])).

tff(c_18171,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_279,c_18168])).

tff(c_18177,plain,(
    k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_15226,c_18171])).

tff(c_18180,plain,(
    k1_funct_1(k5_relat_1('#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18177,c_56])).

tff(c_18190,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_15588,c_18180])).

tff(c_18197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_115,c_66,c_18190])).

tff(c_18198,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_8267])).

tff(c_18216,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18198,c_12])).

tff(c_18219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_18216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:44:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.66/4.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.66/4.42  
% 11.66/4.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.66/4.42  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 11.66/4.42  
% 11.66/4.42  %Foreground sorts:
% 11.66/4.42  
% 11.66/4.42  
% 11.66/4.42  %Background operators:
% 11.66/4.42  
% 11.66/4.42  
% 11.66/4.42  %Foreground operators:
% 11.66/4.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.66/4.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.66/4.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.66/4.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.66/4.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.66/4.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.66/4.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.66/4.42  tff('#skF_7', type, '#skF_7': $i).
% 11.66/4.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.66/4.42  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.66/4.42  tff('#skF_5', type, '#skF_5': $i).
% 11.66/4.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.66/4.42  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 11.66/4.42  tff('#skF_6', type, '#skF_6': $i).
% 11.66/4.42  tff('#skF_3', type, '#skF_3': $i).
% 11.66/4.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.66/4.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.66/4.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.66/4.42  tff('#skF_8', type, '#skF_8': $i).
% 11.66/4.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.66/4.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.66/4.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.66/4.42  tff('#skF_4', type, '#skF_4': $i).
% 11.66/4.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.66/4.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.66/4.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.66/4.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.66/4.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.66/4.42  
% 11.66/4.44  tff(f_170, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 11.66/4.44  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.66/4.44  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.66/4.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.66/4.44  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.66/4.44  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 11.66/4.44  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.66/4.44  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.66/4.44  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 11.66/4.44  tff(f_145, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 11.66/4.44  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.66/4.44  tff(f_117, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_2)).
% 11.66/4.44  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.66/4.44  tff(c_74, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.66/4.44  tff(c_62, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.66/4.44  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.66/4.44  tff(c_103, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.66/4.44  tff(c_115, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_103])).
% 11.66/4.44  tff(c_66, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.66/4.44  tff(c_58, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.66/4.44  tff(c_160, plain, (![A_80, B_81]: (r2_hidden('#skF_2'(A_80, B_81), A_80) | r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.66/4.44  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.66/4.44  tff(c_170, plain, (![A_80, B_81]: (~v1_xboole_0(A_80) | r1_tarski(A_80, B_81))), inference(resolution, [status(thm)], [c_160, c_2])).
% 11.66/4.44  tff(c_89, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | ~m1_subset_1(A_64, k1_zfmisc_1(B_65)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.66/4.44  tff(c_100, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_89])).
% 11.66/4.44  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.66/4.44  tff(c_217, plain, (![C_90, B_91, A_92]: (r2_hidden(C_90, B_91) | ~r2_hidden(C_90, A_92) | ~r1_tarski(A_92, B_91))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.66/4.44  tff(c_3972, plain, (![A_493, B_494, B_495]: (r2_hidden('#skF_2'(A_493, B_494), B_495) | ~r1_tarski(A_493, B_495) | r1_tarski(A_493, B_494))), inference(resolution, [status(thm)], [c_10, c_217])).
% 11.66/4.44  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.66/4.44  tff(c_8308, plain, (![A_881, B_882, B_883, B_884]: (r2_hidden('#skF_2'(A_881, B_882), B_883) | ~r1_tarski(B_884, B_883) | ~r1_tarski(A_881, B_884) | r1_tarski(A_881, B_882))), inference(resolution, [status(thm)], [c_3972, c_6])).
% 11.66/4.44  tff(c_8410, plain, (![A_891, B_892]: (r2_hidden('#skF_2'(A_891, B_892), k2_zfmisc_1('#skF_5', '#skF_3')) | ~r1_tarski(A_891, '#skF_7') | r1_tarski(A_891, B_892))), inference(resolution, [status(thm)], [c_100, c_8308])).
% 11.66/4.44  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.66/4.44  tff(c_8435, plain, (![A_894]: (~r1_tarski(A_894, '#skF_7') | r1_tarski(A_894, k2_zfmisc_1('#skF_5', '#skF_3')))), inference(resolution, [status(thm)], [c_8410, c_8])).
% 11.66/4.44  tff(c_20, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.66/4.44  tff(c_225, plain, (![A_12, B_91, B_13]: (r2_hidden(A_12, B_91) | ~r1_tarski(B_13, B_91) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(resolution, [status(thm)], [c_20, c_217])).
% 11.66/4.44  tff(c_8587, plain, (![A_903, A_904]: (r2_hidden(A_903, k2_zfmisc_1('#skF_5', '#skF_3')) | v1_xboole_0(A_904) | ~m1_subset_1(A_903, A_904) | ~r1_tarski(A_904, '#skF_7'))), inference(resolution, [status(thm)], [c_8435, c_225])).
% 11.66/4.44  tff(c_8599, plain, (r2_hidden('#skF_8', k2_zfmisc_1('#skF_5', '#skF_3')) | v1_xboole_0('#skF_4') | ~r1_tarski('#skF_4', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_8587])).
% 11.66/4.44  tff(c_8600, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_8599])).
% 11.66/4.44  tff(c_8604, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_170, c_8600])).
% 11.66/4.44  tff(c_70, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.66/4.44  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.66/4.44  tff(c_260, plain, (![A_97, B_98, C_99]: (k1_relset_1(A_97, B_98, C_99)=k1_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.66/4.44  tff(c_273, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_260])).
% 11.66/4.44  tff(c_8251, plain, (![B_875, A_876, C_877]: (k1_xboole_0=B_875 | k1_relset_1(A_876, B_875, C_877)=A_876 | ~v1_funct_2(C_877, A_876, B_875) | ~m1_subset_1(C_877, k1_zfmisc_1(k2_zfmisc_1(A_876, B_875))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 11.66/4.44  tff(c_8261, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_8251])).
% 11.66/4.44  tff(c_8267, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_273, c_8261])).
% 11.66/4.44  tff(c_8268, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_8267])).
% 11.66/4.44  tff(c_116, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_103])).
% 11.66/4.44  tff(c_72, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.66/4.44  tff(c_8625, plain, (![B_907, C_908, A_909]: (k1_funct_1(k5_relat_1(B_907, C_908), A_909)=k1_funct_1(C_908, k1_funct_1(B_907, A_909)) | ~r2_hidden(A_909, k1_relat_1(B_907)) | ~v1_funct_1(C_908) | ~v1_relat_1(C_908) | ~v1_funct_1(B_907) | ~v1_relat_1(B_907))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.66/4.44  tff(c_11937, plain, (![B_1212, C_1213, A_1214]: (k1_funct_1(k5_relat_1(B_1212, C_1213), A_1214)=k1_funct_1(C_1213, k1_funct_1(B_1212, A_1214)) | ~v1_funct_1(C_1213) | ~v1_relat_1(C_1213) | ~v1_funct_1(B_1212) | ~v1_relat_1(B_1212) | v1_xboole_0(k1_relat_1(B_1212)) | ~m1_subset_1(A_1214, k1_relat_1(B_1212)))), inference(resolution, [status(thm)], [c_20, c_8625])).
% 11.66/4.44  tff(c_11939, plain, (![C_1213, A_1214]: (k1_funct_1(k5_relat_1('#skF_6', C_1213), A_1214)=k1_funct_1(C_1213, k1_funct_1('#skF_6', A_1214)) | ~v1_funct_1(C_1213) | ~v1_relat_1(C_1213) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | v1_xboole_0(k1_relat_1('#skF_6')) | ~m1_subset_1(A_1214, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8268, c_11937])).
% 11.66/4.44  tff(c_11941, plain, (![C_1213, A_1214]: (k1_funct_1(k5_relat_1('#skF_6', C_1213), A_1214)=k1_funct_1(C_1213, k1_funct_1('#skF_6', A_1214)) | ~v1_funct_1(C_1213) | ~v1_relat_1(C_1213) | v1_xboole_0('#skF_4') | ~m1_subset_1(A_1214, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8268, c_116, c_72, c_11939])).
% 11.66/4.44  tff(c_11942, plain, (![C_1213, A_1214]: (k1_funct_1(k5_relat_1('#skF_6', C_1213), A_1214)=k1_funct_1(C_1213, k1_funct_1('#skF_6', A_1214)) | ~v1_funct_1(C_1213) | ~v1_relat_1(C_1213) | ~m1_subset_1(A_1214, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_8604, c_11941])).
% 11.66/4.44  tff(c_8692, plain, (![E_912, D_914, F_915, B_917, A_913, C_916]: (k1_partfun1(A_913, B_917, C_916, D_914, E_912, F_915)=k5_relat_1(E_912, F_915) | ~m1_subset_1(F_915, k1_zfmisc_1(k2_zfmisc_1(C_916, D_914))) | ~v1_funct_1(F_915) | ~m1_subset_1(E_912, k1_zfmisc_1(k2_zfmisc_1(A_913, B_917))) | ~v1_funct_1(E_912))), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.66/4.44  tff(c_8697, plain, (![A_913, B_917, E_912]: (k1_partfun1(A_913, B_917, '#skF_5', '#skF_3', E_912, '#skF_7')=k5_relat_1(E_912, '#skF_7') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_912, k1_zfmisc_1(k2_zfmisc_1(A_913, B_917))) | ~v1_funct_1(E_912))), inference(resolution, [status(thm)], [c_64, c_8692])).
% 11.66/4.44  tff(c_11702, plain, (![A_1195, B_1196, E_1197]: (k1_partfun1(A_1195, B_1196, '#skF_5', '#skF_3', E_1197, '#skF_7')=k5_relat_1(E_1197, '#skF_7') | ~m1_subset_1(E_1197, k1_zfmisc_1(k2_zfmisc_1(A_1195, B_1196))) | ~v1_funct_1(E_1197))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_8697])).
% 11.66/4.44  tff(c_11712, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_11702])).
% 11.66/4.44  tff(c_11719, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_11712])).
% 11.66/4.44  tff(c_272, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_260])).
% 11.66/4.44  tff(c_60, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.66/4.44  tff(c_279, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_60])).
% 11.66/4.44  tff(c_101, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_68, c_89])).
% 11.66/4.44  tff(c_8324, plain, (![A_885, B_886]: (r2_hidden('#skF_2'(A_885, B_886), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(A_885, '#skF_6') | r1_tarski(A_885, B_886))), inference(resolution, [status(thm)], [c_101, c_8308])).
% 11.66/4.44  tff(c_8335, plain, (![A_885]: (~r1_tarski(A_885, '#skF_6') | r1_tarski(A_885, k2_zfmisc_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_8324, c_8])).
% 11.66/4.44  tff(c_24, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.66/4.44  tff(c_8865, plain, (![B_935, A_936, A_937]: (k1_xboole_0=B_935 | k1_relset_1(A_936, B_935, A_937)=A_936 | ~v1_funct_2(A_937, A_936, B_935) | ~r1_tarski(A_937, k2_zfmisc_1(A_936, B_935)))), inference(resolution, [status(thm)], [c_24, c_8251])).
% 11.66/4.44  tff(c_8887, plain, (![A_885]: (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', A_885)='#skF_4' | ~v1_funct_2(A_885, '#skF_4', '#skF_5') | ~r1_tarski(A_885, '#skF_6'))), inference(resolution, [status(thm)], [c_8335, c_8865])).
% 11.66/4.44  tff(c_11265, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_8887])).
% 11.66/4.44  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.66/4.44  tff(c_11324, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11265, c_12])).
% 11.66/4.44  tff(c_11327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_11324])).
% 11.66/4.44  tff(c_11329, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_8887])).
% 11.66/4.44  tff(c_8791, plain, (![C_927, A_926, B_924, D_923, E_925]: (k1_partfun1(A_926, B_924, B_924, C_927, D_923, E_925)=k8_funct_2(A_926, B_924, C_927, D_923, E_925) | k1_xboole_0=B_924 | ~r1_tarski(k2_relset_1(A_926, B_924, D_923), k1_relset_1(B_924, C_927, E_925)) | ~m1_subset_1(E_925, k1_zfmisc_1(k2_zfmisc_1(B_924, C_927))) | ~v1_funct_1(E_925) | ~m1_subset_1(D_923, k1_zfmisc_1(k2_zfmisc_1(A_926, B_924))) | ~v1_funct_2(D_923, A_926, B_924) | ~v1_funct_1(D_923))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.66/4.44  tff(c_8803, plain, (![A_926, D_923]: (k1_partfun1(A_926, '#skF_5', '#skF_5', '#skF_3', D_923, '#skF_7')=k8_funct_2(A_926, '#skF_5', '#skF_3', D_923, '#skF_7') | k1_xboole_0='#skF_5' | ~r1_tarski(k2_relset_1(A_926, '#skF_5', D_923), k1_relat_1('#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_923, k1_zfmisc_1(k2_zfmisc_1(A_926, '#skF_5'))) | ~v1_funct_2(D_923, A_926, '#skF_5') | ~v1_funct_1(D_923))), inference(superposition, [status(thm), theory('equality')], [c_272, c_8791])).
% 11.66/4.44  tff(c_8813, plain, (![A_926, D_923]: (k1_partfun1(A_926, '#skF_5', '#skF_5', '#skF_3', D_923, '#skF_7')=k8_funct_2(A_926, '#skF_5', '#skF_3', D_923, '#skF_7') | k1_xboole_0='#skF_5' | ~r1_tarski(k2_relset_1(A_926, '#skF_5', D_923), k1_relat_1('#skF_7')) | ~m1_subset_1(D_923, k1_zfmisc_1(k2_zfmisc_1(A_926, '#skF_5'))) | ~v1_funct_2(D_923, A_926, '#skF_5') | ~v1_funct_1(D_923))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_8803])).
% 11.66/4.44  tff(c_14457, plain, (![A_1405, D_1406]: (k1_partfun1(A_1405, '#skF_5', '#skF_5', '#skF_3', D_1406, '#skF_7')=k8_funct_2(A_1405, '#skF_5', '#skF_3', D_1406, '#skF_7') | ~r1_tarski(k2_relset_1(A_1405, '#skF_5', D_1406), k1_relat_1('#skF_7')) | ~m1_subset_1(D_1406, k1_zfmisc_1(k2_zfmisc_1(A_1405, '#skF_5'))) | ~v1_funct_2(D_1406, A_1405, '#skF_5') | ~v1_funct_1(D_1406))), inference(negUnitSimplification, [status(thm)], [c_11329, c_8813])).
% 11.66/4.44  tff(c_14469, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_279, c_14457])).
% 11.66/4.44  tff(c_14475, plain, (k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_11719, c_14469])).
% 11.66/4.44  tff(c_56, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.66/4.44  tff(c_14508, plain, (k1_funct_1(k5_relat_1('#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_14475, c_56])).
% 11.66/4.44  tff(c_14515, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11942, c_14508])).
% 11.66/4.44  tff(c_14522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_115, c_66, c_14515])).
% 11.66/4.44  tff(c_14524, plain, (r1_tarski('#skF_4', '#skF_7')), inference(splitRight, [status(thm)], [c_8599])).
% 11.66/4.44  tff(c_14552, plain, (![A_12]: (r2_hidden(A_12, '#skF_7') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_12, '#skF_4'))), inference(resolution, [status(thm)], [c_14524, c_225])).
% 11.66/4.44  tff(c_14632, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_14552])).
% 11.66/4.44  tff(c_171, plain, (![A_82, B_83]: (~v1_xboole_0(A_82) | r1_tarski(A_82, B_83))), inference(resolution, [status(thm)], [c_160, c_2])).
% 11.66/4.44  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.66/4.44  tff(c_185, plain, (![B_85, A_86]: (B_85=A_86 | ~r1_tarski(B_85, A_86) | ~v1_xboole_0(A_86))), inference(resolution, [status(thm)], [c_171, c_14])).
% 11.66/4.44  tff(c_207, plain, (![B_87, A_88]: (B_87=A_88 | ~v1_xboole_0(B_87) | ~v1_xboole_0(A_88))), inference(resolution, [status(thm)], [c_170, c_185])).
% 11.66/4.44  tff(c_210, plain, (![A_88]: (k1_xboole_0=A_88 | ~v1_xboole_0(A_88))), inference(resolution, [status(thm)], [c_12, c_207])).
% 11.66/4.44  tff(c_14637, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_14632, c_210])).
% 11.66/4.44  tff(c_14650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_14637])).
% 11.66/4.44  tff(c_14652, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_14552])).
% 11.66/4.44  tff(c_14556, plain, (![B_1408, C_1409, A_1410]: (k1_funct_1(k5_relat_1(B_1408, C_1409), A_1410)=k1_funct_1(C_1409, k1_funct_1(B_1408, A_1410)) | ~r2_hidden(A_1410, k1_relat_1(B_1408)) | ~v1_funct_1(C_1409) | ~v1_relat_1(C_1409) | ~v1_funct_1(B_1408) | ~v1_relat_1(B_1408))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.66/4.44  tff(c_15583, plain, (![B_1503, C_1504, A_1505]: (k1_funct_1(k5_relat_1(B_1503, C_1504), A_1505)=k1_funct_1(C_1504, k1_funct_1(B_1503, A_1505)) | ~v1_funct_1(C_1504) | ~v1_relat_1(C_1504) | ~v1_funct_1(B_1503) | ~v1_relat_1(B_1503) | v1_xboole_0(k1_relat_1(B_1503)) | ~m1_subset_1(A_1505, k1_relat_1(B_1503)))), inference(resolution, [status(thm)], [c_20, c_14556])).
% 11.66/4.44  tff(c_15585, plain, (![C_1504, A_1505]: (k1_funct_1(k5_relat_1('#skF_6', C_1504), A_1505)=k1_funct_1(C_1504, k1_funct_1('#skF_6', A_1505)) | ~v1_funct_1(C_1504) | ~v1_relat_1(C_1504) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | v1_xboole_0(k1_relat_1('#skF_6')) | ~m1_subset_1(A_1505, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8268, c_15583])).
% 11.66/4.44  tff(c_15587, plain, (![C_1504, A_1505]: (k1_funct_1(k5_relat_1('#skF_6', C_1504), A_1505)=k1_funct_1(C_1504, k1_funct_1('#skF_6', A_1505)) | ~v1_funct_1(C_1504) | ~v1_relat_1(C_1504) | v1_xboole_0('#skF_4') | ~m1_subset_1(A_1505, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8268, c_116, c_72, c_15585])).
% 11.66/4.44  tff(c_15588, plain, (![C_1504, A_1505]: (k1_funct_1(k5_relat_1('#skF_6', C_1504), A_1505)=k1_funct_1(C_1504, k1_funct_1('#skF_6', A_1505)) | ~v1_funct_1(C_1504) | ~v1_relat_1(C_1504) | ~m1_subset_1(A_1505, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_14652, c_15587])).
% 11.66/4.44  tff(c_14617, plain, (![A_1412, C_1415, D_1413, B_1416, F_1414, E_1411]: (k1_partfun1(A_1412, B_1416, C_1415, D_1413, E_1411, F_1414)=k5_relat_1(E_1411, F_1414) | ~m1_subset_1(F_1414, k1_zfmisc_1(k2_zfmisc_1(C_1415, D_1413))) | ~v1_funct_1(F_1414) | ~m1_subset_1(E_1411, k1_zfmisc_1(k2_zfmisc_1(A_1412, B_1416))) | ~v1_funct_1(E_1411))), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.66/4.44  tff(c_14622, plain, (![A_1412, B_1416, E_1411]: (k1_partfun1(A_1412, B_1416, '#skF_5', '#skF_3', E_1411, '#skF_7')=k5_relat_1(E_1411, '#skF_7') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1411, k1_zfmisc_1(k2_zfmisc_1(A_1412, B_1416))) | ~v1_funct_1(E_1411))), inference(resolution, [status(thm)], [c_64, c_14617])).
% 11.66/4.44  tff(c_15209, plain, (![A_1460, B_1461, E_1462]: (k1_partfun1(A_1460, B_1461, '#skF_5', '#skF_3', E_1462, '#skF_7')=k5_relat_1(E_1462, '#skF_7') | ~m1_subset_1(E_1462, k1_zfmisc_1(k2_zfmisc_1(A_1460, B_1461))) | ~v1_funct_1(E_1462))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_14622])).
% 11.66/4.44  tff(c_15219, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_15209])).
% 11.66/4.44  tff(c_15226, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_15219])).
% 11.66/4.44  tff(c_8337, plain, (![B_887, C_888, A_889]: (k1_xboole_0=B_887 | v1_funct_2(C_888, A_889, B_887) | k1_relset_1(A_889, B_887, C_888)!=A_889 | ~m1_subset_1(C_888, k1_zfmisc_1(k2_zfmisc_1(A_889, B_887))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 11.66/4.44  tff(c_14802, plain, (![B_1433, A_1434, A_1435]: (k1_xboole_0=B_1433 | v1_funct_2(A_1434, A_1435, B_1433) | k1_relset_1(A_1435, B_1433, A_1434)!=A_1435 | ~r1_tarski(A_1434, k2_zfmisc_1(A_1435, B_1433)))), inference(resolution, [status(thm)], [c_24, c_8337])).
% 11.66/4.44  tff(c_14824, plain, (![A_885]: (k1_xboole_0='#skF_5' | v1_funct_2(A_885, '#skF_4', '#skF_5') | k1_relset_1('#skF_4', '#skF_5', A_885)!='#skF_4' | ~r1_tarski(A_885, '#skF_6'))), inference(resolution, [status(thm)], [c_8335, c_14802])).
% 11.66/4.44  tff(c_16564, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_14824])).
% 11.66/4.44  tff(c_16616, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16564, c_12])).
% 11.66/4.44  tff(c_16619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_16616])).
% 11.66/4.44  tff(c_16621, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_14824])).
% 11.66/4.44  tff(c_14695, plain, (![B_1421, A_1423, C_1424, D_1420, E_1422]: (k1_partfun1(A_1423, B_1421, B_1421, C_1424, D_1420, E_1422)=k8_funct_2(A_1423, B_1421, C_1424, D_1420, E_1422) | k1_xboole_0=B_1421 | ~r1_tarski(k2_relset_1(A_1423, B_1421, D_1420), k1_relset_1(B_1421, C_1424, E_1422)) | ~m1_subset_1(E_1422, k1_zfmisc_1(k2_zfmisc_1(B_1421, C_1424))) | ~v1_funct_1(E_1422) | ~m1_subset_1(D_1420, k1_zfmisc_1(k2_zfmisc_1(A_1423, B_1421))) | ~v1_funct_2(D_1420, A_1423, B_1421) | ~v1_funct_1(D_1420))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.66/4.44  tff(c_14710, plain, (![A_1423, D_1420]: (k1_partfun1(A_1423, '#skF_5', '#skF_5', '#skF_3', D_1420, '#skF_7')=k8_funct_2(A_1423, '#skF_5', '#skF_3', D_1420, '#skF_7') | k1_xboole_0='#skF_5' | ~r1_tarski(k2_relset_1(A_1423, '#skF_5', D_1420), k1_relat_1('#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_1420, k1_zfmisc_1(k2_zfmisc_1(A_1423, '#skF_5'))) | ~v1_funct_2(D_1420, A_1423, '#skF_5') | ~v1_funct_1(D_1420))), inference(superposition, [status(thm), theory('equality')], [c_272, c_14695])).
% 11.66/4.44  tff(c_14720, plain, (![A_1423, D_1420]: (k1_partfun1(A_1423, '#skF_5', '#skF_5', '#skF_3', D_1420, '#skF_7')=k8_funct_2(A_1423, '#skF_5', '#skF_3', D_1420, '#skF_7') | k1_xboole_0='#skF_5' | ~r1_tarski(k2_relset_1(A_1423, '#skF_5', D_1420), k1_relat_1('#skF_7')) | ~m1_subset_1(D_1420, k1_zfmisc_1(k2_zfmisc_1(A_1423, '#skF_5'))) | ~v1_funct_2(D_1420, A_1423, '#skF_5') | ~v1_funct_1(D_1420))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_14710])).
% 11.66/4.44  tff(c_18168, plain, (![A_1653, D_1654]: (k1_partfun1(A_1653, '#skF_5', '#skF_5', '#skF_3', D_1654, '#skF_7')=k8_funct_2(A_1653, '#skF_5', '#skF_3', D_1654, '#skF_7') | ~r1_tarski(k2_relset_1(A_1653, '#skF_5', D_1654), k1_relat_1('#skF_7')) | ~m1_subset_1(D_1654, k1_zfmisc_1(k2_zfmisc_1(A_1653, '#skF_5'))) | ~v1_funct_2(D_1654, A_1653, '#skF_5') | ~v1_funct_1(D_1654))), inference(negUnitSimplification, [status(thm)], [c_16621, c_14720])).
% 11.66/4.44  tff(c_18171, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_279, c_18168])).
% 11.66/4.44  tff(c_18177, plain, (k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_15226, c_18171])).
% 11.66/4.44  tff(c_18180, plain, (k1_funct_1(k5_relat_1('#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_18177, c_56])).
% 11.66/4.44  tff(c_18190, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_15588, c_18180])).
% 11.66/4.44  tff(c_18197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_115, c_66, c_18190])).
% 11.66/4.44  tff(c_18198, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_8267])).
% 11.66/4.44  tff(c_18216, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18198, c_12])).
% 11.66/4.44  tff(c_18219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_18216])).
% 11.66/4.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.66/4.44  
% 11.66/4.44  Inference rules
% 11.66/4.44  ----------------------
% 11.66/4.44  #Ref     : 14
% 11.66/4.44  #Sup     : 3827
% 11.66/4.44  #Fact    : 0
% 11.66/4.44  #Define  : 0
% 11.66/4.44  #Split   : 130
% 11.66/4.44  #Chain   : 0
% 11.66/4.44  #Close   : 0
% 11.66/4.44  
% 11.66/4.44  Ordering : KBO
% 11.66/4.44  
% 11.66/4.44  Simplification rules
% 11.66/4.44  ----------------------
% 11.66/4.44  #Subsume      : 1668
% 11.66/4.44  #Demod        : 2810
% 11.66/4.44  #Tautology    : 1019
% 11.66/4.44  #SimpNegUnit  : 323
% 11.66/4.44  #BackRed      : 682
% 11.66/4.44  
% 11.66/4.44  #Partial instantiations: 0
% 11.66/4.44  #Strategies tried      : 1
% 11.66/4.44  
% 11.66/4.44  Timing (in seconds)
% 11.66/4.44  ----------------------
% 11.66/4.45  Preprocessing        : 0.37
% 11.66/4.45  Parsing              : 0.19
% 11.66/4.45  CNF conversion       : 0.03
% 11.66/4.45  Main loop            : 3.30
% 11.66/4.45  Inferencing          : 0.94
% 11.66/4.45  Reduction            : 1.15
% 11.66/4.45  Demodulation         : 0.75
% 11.66/4.45  BG Simplification    : 0.09
% 11.66/4.45  Subsumption          : 0.88
% 11.66/4.45  Abstraction          : 0.12
% 11.66/4.45  MUC search           : 0.00
% 11.66/4.45  Cooper               : 0.00
% 11.66/4.45  Total                : 3.71
% 11.66/4.45  Index Insertion      : 0.00
% 11.66/4.45  Index Deletion       : 0.00
% 11.66/4.45  Index Matching       : 0.00
% 11.66/4.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
