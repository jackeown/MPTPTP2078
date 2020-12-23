%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:01 EST 2020

% Result     : Theorem 12.79s
% Output     : CNFRefutation 12.91s
% Verified   : 
% Statistics : Number of formulae       :  150 (1537 expanded)
%              Number of leaves         :   57 ( 495 expanded)
%              Depth                    :   20
%              Number of atoms          :  226 (4424 expanded)
%              Number of equality atoms :   39 (1594 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_17 > #skF_6 > #skF_15 > #skF_1 > #skF_10 > #skF_9 > #skF_12 > #skF_8 > #skF_16 > #skF_14 > #skF_2 > #skF_11 > #skF_7 > #skF_3 > #skF_13 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_13',type,(
    '#skF_13': ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_225,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_hidden(D,k5_partfun1(A,B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

tff(f_111,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_165,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_204,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( D = k5_partfun1(A,B,C)
        <=> ! [E] :
              ( r2_hidden(E,D)
            <=> ? [F] :
                  ( v1_funct_1(F)
                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                  & F = E
                  & v1_partfun1(F,A)
                  & r1_partfun1(C,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_96,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_93,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_151,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_62,axiom,(
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

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,
    ( k1_xboole_0 = '#skF_14'
    | k1_xboole_0 != '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_151,plain,(
    k1_xboole_0 != '#skF_15' ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_128,plain,(
    ~ r2_hidden('#skF_17',k5_partfun1('#skF_14','#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_142,plain,(
    v1_funct_1('#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_132,plain,(
    r1_partfun1('#skF_16','#skF_17') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_140,plain,(
    m1_subset_1('#skF_16',k1_zfmisc_1(k2_zfmisc_1('#skF_14','#skF_15'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_138,plain,(
    v1_funct_1('#skF_17') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_134,plain,(
    m1_subset_1('#skF_17',k1_zfmisc_1(k2_zfmisc_1('#skF_14','#skF_15'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_368,plain,(
    ! [C_159,B_160,A_161] :
      ( v1_xboole_0(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(B_160,A_161)))
      | ~ v1_xboole_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_375,plain,
    ( v1_xboole_0('#skF_17')
    | ~ v1_xboole_0('#skF_15') ),
    inference(resolution,[status(thm)],[c_134,c_368])).

tff(c_389,plain,(
    ~ v1_xboole_0('#skF_15') ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_136,plain,(
    v1_funct_2('#skF_17','#skF_14','#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_5700,plain,(
    ! [C_391,A_392,B_393] :
      ( v1_partfun1(C_391,A_392)
      | ~ v1_funct_2(C_391,A_392,B_393)
      | ~ v1_funct_1(C_391)
      | ~ m1_subset_1(C_391,k1_zfmisc_1(k2_zfmisc_1(A_392,B_393)))
      | v1_xboole_0(B_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_5707,plain,
    ( v1_partfun1('#skF_17','#skF_14')
    | ~ v1_funct_2('#skF_17','#skF_14','#skF_15')
    | ~ v1_funct_1('#skF_17')
    | v1_xboole_0('#skF_15') ),
    inference(resolution,[status(thm)],[c_134,c_5700])).

tff(c_5714,plain,
    ( v1_partfun1('#skF_17','#skF_14')
    | v1_xboole_0('#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_136,c_5707])).

tff(c_5715,plain,(
    v1_partfun1('#skF_17','#skF_14') ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_5714])).

tff(c_16916,plain,(
    ! [F_632,A_633,B_634,C_635] :
      ( r2_hidden(F_632,k5_partfun1(A_633,B_634,C_635))
      | ~ r1_partfun1(C_635,F_632)
      | ~ v1_partfun1(F_632,A_633)
      | ~ m1_subset_1(F_632,k1_zfmisc_1(k2_zfmisc_1(A_633,B_634)))
      | ~ v1_funct_1(F_632)
      | ~ m1_subset_1(C_635,k1_zfmisc_1(k2_zfmisc_1(A_633,B_634)))
      | ~ v1_funct_1(C_635) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_16921,plain,(
    ! [C_635] :
      ( r2_hidden('#skF_17',k5_partfun1('#skF_14','#skF_15',C_635))
      | ~ r1_partfun1(C_635,'#skF_17')
      | ~ v1_partfun1('#skF_17','#skF_14')
      | ~ v1_funct_1('#skF_17')
      | ~ m1_subset_1(C_635,k1_zfmisc_1(k2_zfmisc_1('#skF_14','#skF_15')))
      | ~ v1_funct_1(C_635) ) ),
    inference(resolution,[status(thm)],[c_134,c_16916])).

tff(c_17242,plain,(
    ! [C_645] :
      ( r2_hidden('#skF_17',k5_partfun1('#skF_14','#skF_15',C_645))
      | ~ r1_partfun1(C_645,'#skF_17')
      | ~ m1_subset_1(C_645,k1_zfmisc_1(k2_zfmisc_1('#skF_14','#skF_15')))
      | ~ v1_funct_1(C_645) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_5715,c_16921])).

tff(c_17252,plain,
    ( r2_hidden('#skF_17',k5_partfun1('#skF_14','#skF_15','#skF_16'))
    | ~ r1_partfun1('#skF_16','#skF_17')
    | ~ v1_funct_1('#skF_16') ),
    inference(resolution,[status(thm)],[c_140,c_17242])).

tff(c_17259,plain,(
    r2_hidden('#skF_17',k5_partfun1('#skF_14','#skF_15','#skF_16')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_132,c_17252])).

tff(c_17261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_17259])).

tff(c_17263,plain,(
    v1_xboole_0('#skF_15') ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_34,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_17280,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(resolution,[status(thm)],[c_17263,c_34])).

tff(c_17286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_17280])).

tff(c_17287,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_17288,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_17295,plain,(
    '#skF_15' = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17287,c_17288])).

tff(c_17332,plain,(
    m1_subset_1('#skF_17',k1_zfmisc_1(k2_zfmisc_1('#skF_14','#skF_14'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17295,c_134])).

tff(c_17399,plain,(
    ! [C_674,A_675,B_676] :
      ( v1_relat_1(C_674)
      | ~ m1_subset_1(C_674,k1_zfmisc_1(k2_zfmisc_1(A_675,B_676))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_17406,plain,(
    v1_relat_1('#skF_17') ),
    inference(resolution,[status(thm)],[c_17332,c_17399])).

tff(c_44,plain,(
    ! [A_26] :
      ( k7_relat_1(A_26,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_17322,plain,(
    ! [A_26] :
      ( k7_relat_1(A_26,'#skF_14') = '#skF_14'
      | ~ v1_relat_1(A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17287,c_17287,c_44])).

tff(c_17411,plain,(
    k7_relat_1('#skF_17','#skF_14') = '#skF_14' ),
    inference(resolution,[status(thm)],[c_17406,c_17322])).

tff(c_42,plain,(
    ! [A_24,B_25] :
      ( v1_relat_1(k7_relat_1(A_24,B_25))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_17419,plain,
    ( v1_relat_1('#skF_14')
    | ~ v1_relat_1('#skF_17') ),
    inference(superposition,[status(thm),theory(equality)],[c_17411,c_42])).

tff(c_17423,plain,(
    v1_relat_1('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17406,c_17419])).

tff(c_50,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_17290,plain,(
    k1_relat_1('#skF_14') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17287,c_17287,c_50])).

tff(c_46,plain,(
    ! [A_27] : k7_relat_1(k1_xboole_0,A_27) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_17309,plain,(
    ! [A_27] : k7_relat_1('#skF_14',A_27) = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17287,c_17287,c_46])).

tff(c_17487,plain,(
    ! [B_684,A_685] :
      ( k3_xboole_0(k1_relat_1(B_684),A_685) = k1_relat_1(k7_relat_1(B_684,A_685))
      | ~ v1_relat_1(B_684) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_17502,plain,(
    ! [A_685] :
      ( k1_relat_1(k7_relat_1('#skF_14',A_685)) = k3_xboole_0('#skF_14',A_685)
      | ~ v1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17290,c_17487])).

tff(c_17507,plain,(
    ! [A_686] : k3_xboole_0('#skF_14',A_686) = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17423,c_17290,c_17309,c_17502])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_17520,plain,(
    ! [D_687,A_688] :
      ( r2_hidden(D_687,A_688)
      | ~ r2_hidden(D_687,'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17507,c_8])).

tff(c_17532,plain,(
    ! [A_688] :
      ( r2_hidden('#skF_1'('#skF_14'),A_688)
      | v1_xboole_0('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_4,c_17520])).

tff(c_17533,plain,(
    v1_xboole_0('#skF_14') ),
    inference(splitLeft,[status(thm)],[c_17532])).

tff(c_17319,plain,(
    m1_subset_1('#skF_16',k1_zfmisc_1(k2_zfmisc_1('#skF_14','#skF_14'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17295,c_140])).

tff(c_17534,plain,(
    ! [C_689,B_690,A_691] :
      ( v1_xboole_0(C_689)
      | ~ m1_subset_1(C_689,k1_zfmisc_1(k2_zfmisc_1(B_690,A_691)))
      | ~ v1_xboole_0(A_691) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_17542,plain,
    ( v1_xboole_0('#skF_16')
    | ~ v1_xboole_0('#skF_14') ),
    inference(resolution,[status(thm)],[c_17319,c_17534])).

tff(c_17590,plain,(
    v1_xboole_0('#skF_16') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17533,c_17542])).

tff(c_17317,plain,(
    ! [A_18] :
      ( A_18 = '#skF_14'
      | ~ v1_xboole_0(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17287,c_34])).

tff(c_17600,plain,(
    '#skF_16' = '#skF_14' ),
    inference(resolution,[status(thm)],[c_17590,c_17317])).

tff(c_17541,plain,
    ( v1_xboole_0('#skF_17')
    | ~ v1_xboole_0('#skF_14') ),
    inference(resolution,[status(thm)],[c_17332,c_17534])).

tff(c_17556,plain,(
    v1_xboole_0('#skF_17') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17533,c_17541])).

tff(c_17566,plain,(
    '#skF_17' = '#skF_14' ),
    inference(resolution,[status(thm)],[c_17556,c_17317])).

tff(c_17321,plain,(
    ~ r2_hidden('#skF_17',k5_partfun1('#skF_14','#skF_14','#skF_16')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17295,c_128])).

tff(c_17571,plain,(
    ~ r2_hidden('#skF_14',k5_partfun1('#skF_14','#skF_14','#skF_16')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17566,c_17321])).

tff(c_17683,plain,(
    ~ r2_hidden('#skF_14',k5_partfun1('#skF_14','#skF_14','#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17600,c_17571])).

tff(c_17574,plain,(
    v1_funct_1('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17566,c_138])).

tff(c_17573,plain,(
    r1_partfun1('#skF_16','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17566,c_132])).

tff(c_17603,plain,(
    r1_partfun1('#skF_14','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17600,c_17573])).

tff(c_17606,plain,(
    m1_subset_1('#skF_14',k1_zfmisc_1(k2_zfmisc_1('#skF_14','#skF_14'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17600,c_17319])).

tff(c_17582,plain,(
    ! [C_692,A_693,B_694] :
      ( v1_partfun1(C_692,A_693)
      | ~ m1_subset_1(C_692,k1_zfmisc_1(k2_zfmisc_1(A_693,B_694)))
      | ~ v1_xboole_0(A_693) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_17585,plain,
    ( v1_partfun1('#skF_16','#skF_14')
    | ~ v1_xboole_0('#skF_14') ),
    inference(resolution,[status(thm)],[c_17319,c_17582])).

tff(c_17588,plain,(
    v1_partfun1('#skF_16','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17533,c_17585])).

tff(c_17602,plain,(
    v1_partfun1('#skF_14','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17600,c_17588])).

tff(c_41006,plain,(
    ! [F_1318,A_1319,B_1320,C_1321] :
      ( r2_hidden(F_1318,k5_partfun1(A_1319,B_1320,C_1321))
      | ~ r1_partfun1(C_1321,F_1318)
      | ~ v1_partfun1(F_1318,A_1319)
      | ~ m1_subset_1(F_1318,k1_zfmisc_1(k2_zfmisc_1(A_1319,B_1320)))
      | ~ v1_funct_1(F_1318)
      | ~ m1_subset_1(C_1321,k1_zfmisc_1(k2_zfmisc_1(A_1319,B_1320)))
      | ~ v1_funct_1(C_1321) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_41008,plain,(
    ! [C_1321] :
      ( r2_hidden('#skF_14',k5_partfun1('#skF_14','#skF_14',C_1321))
      | ~ r1_partfun1(C_1321,'#skF_14')
      | ~ v1_partfun1('#skF_14','#skF_14')
      | ~ v1_funct_1('#skF_14')
      | ~ m1_subset_1(C_1321,k1_zfmisc_1(k2_zfmisc_1('#skF_14','#skF_14')))
      | ~ v1_funct_1(C_1321) ) ),
    inference(resolution,[status(thm)],[c_17606,c_41006])).

tff(c_41886,plain,(
    ! [C_1328] :
      ( r2_hidden('#skF_14',k5_partfun1('#skF_14','#skF_14',C_1328))
      | ~ r1_partfun1(C_1328,'#skF_14')
      | ~ m1_subset_1(C_1328,k1_zfmisc_1(k2_zfmisc_1('#skF_14','#skF_14')))
      | ~ v1_funct_1(C_1328) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17574,c_17602,c_41008])).

tff(c_41889,plain,
    ( r2_hidden('#skF_14',k5_partfun1('#skF_14','#skF_14','#skF_14'))
    | ~ r1_partfun1('#skF_14','#skF_14')
    | ~ v1_funct_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_17606,c_41886])).

tff(c_41896,plain,(
    r2_hidden('#skF_14',k5_partfun1('#skF_14','#skF_14','#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17574,c_17603,c_41889])).

tff(c_41898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17683,c_41896])).

tff(c_41901,plain,(
    ! [A_1329] : r2_hidden('#skF_1'('#skF_14'),A_1329) ),
    inference(splitRight,[status(thm)],[c_17532])).

tff(c_36,plain,(
    ! [B_20,A_19] :
      ( ~ v1_xboole_0(B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_41922,plain,(
    ! [A_1329] : ~ v1_xboole_0(A_1329) ),
    inference(resolution,[status(thm)],[c_41901,c_36])).

tff(c_41925,plain,(
    ! [A_1331] : r2_hidden('#skF_1'(A_1331),A_1331) ),
    inference(negUnitSimplification,[status(thm)],[c_41922,c_4])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( r2_hidden(D_10,A_5)
      | ~ r2_hidden(D_10,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_41941,plain,(
    ! [A_1332,B_1333] : r2_hidden('#skF_1'(k3_xboole_0(A_1332,B_1333)),A_1332) ),
    inference(resolution,[status(thm)],[c_41925,c_10])).

tff(c_42013,plain,(
    ! [A_1338,B_1339,B_1340] : r2_hidden('#skF_1'(k3_xboole_0(k3_xboole_0(A_1338,B_1339),B_1340)),B_1339) ),
    inference(resolution,[status(thm)],[c_41941,c_8])).

tff(c_17515,plain,(
    ! [D_10,A_686] :
      ( r2_hidden(D_10,A_686)
      | ~ r2_hidden(D_10,'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17507,c_8])).

tff(c_42031,plain,(
    ! [A_1338,B_1340,A_686] : r2_hidden('#skF_1'(k3_xboole_0(k3_xboole_0(A_1338,'#skF_14'),B_1340)),A_686) ),
    inference(resolution,[status(thm)],[c_42013,c_17515])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(A_11,B_12)
      | k3_xboole_0(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_17338,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(A_11,B_12)
      | k3_xboole_0(A_11,B_12) != '#skF_14' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17287,c_26])).

tff(c_17477,plain,(
    ! [A_681,B_682,C_683] :
      ( ~ r1_xboole_0(A_681,B_682)
      | ~ r2_hidden(C_683,B_682)
      | ~ r2_hidden(C_683,A_681) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_42304,plain,(
    ! [C_1368,B_1369,A_1370] :
      ( ~ r2_hidden(C_1368,B_1369)
      | ~ r2_hidden(C_1368,A_1370)
      | k3_xboole_0(A_1370,B_1369) != '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_17338,c_17477])).

tff(c_42312,plain,(
    ! [A_1338,B_1340,A_1370,A_686] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0(k3_xboole_0(A_1338,'#skF_14'),B_1340)),A_1370)
      | k3_xboole_0(A_1370,A_686) != '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_42031,c_42304])).

tff(c_42346,plain,(
    ! [A_1370,A_686] : k3_xboole_0(A_1370,A_686) != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42031,c_42312])).

tff(c_17506,plain,(
    ! [A_685] : k3_xboole_0('#skF_14',A_685) = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17423,c_17290,c_17309,c_17502])).

tff(c_42369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42346,c_17506])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:05:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.79/5.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.91/5.15  
% 12.91/5.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.91/5.15  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_17 > #skF_6 > #skF_15 > #skF_1 > #skF_10 > #skF_9 > #skF_12 > #skF_8 > #skF_16 > #skF_14 > #skF_2 > #skF_11 > #skF_7 > #skF_3 > #skF_13 > #skF_5 > #skF_4
% 12.91/5.15  
% 12.91/5.15  %Foreground sorts:
% 12.91/5.15  
% 12.91/5.15  
% 12.91/5.15  %Background operators:
% 12.91/5.15  
% 12.91/5.15  
% 12.91/5.15  %Foreground operators:
% 12.91/5.15  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.91/5.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.91/5.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.91/5.15  tff('#skF_17', type, '#skF_17': $i).
% 12.91/5.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.91/5.15  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 12.91/5.15  tff('#skF_15', type, '#skF_15': $i).
% 12.91/5.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.91/5.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 12.91/5.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.91/5.15  tff('#skF_10', type, '#skF_10': ($i * $i * $i * $i) > $i).
% 12.91/5.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.91/5.15  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 12.91/5.15  tff('#skF_12', type, '#skF_12': ($i * $i * $i * $i) > $i).
% 12.91/5.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.91/5.15  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 12.91/5.15  tff('#skF_16', type, '#skF_16': $i).
% 12.91/5.15  tff('#skF_14', type, '#skF_14': $i).
% 12.91/5.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.91/5.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.91/5.15  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 12.91/5.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.91/5.15  tff('#skF_11', type, '#skF_11': ($i * $i * $i * $i) > $i).
% 12.91/5.15  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 12.91/5.15  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.91/5.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.91/5.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.91/5.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.91/5.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.91/5.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.91/5.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.91/5.15  tff('#skF_13', type, '#skF_13': ($i * $i * $i * $i * $i) > $i).
% 12.91/5.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.91/5.15  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 12.91/5.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.91/5.15  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 12.91/5.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.91/5.15  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 12.91/5.15  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.91/5.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.91/5.15  
% 12.91/5.17  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 12.91/5.17  tff(f_225, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_hidden(D, k5_partfun1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_2)).
% 12.91/5.17  tff(f_111, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 12.91/5.17  tff(f_165, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 12.91/5.17  tff(f_204, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 12.91/5.17  tff(f_66, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 12.91/5.17  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.91/5.17  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 12.91/5.17  tff(f_87, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 12.91/5.17  tff(f_96, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 12.91/5.17  tff(f_93, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 12.91/5.17  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 12.91/5.17  tff(f_40, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 12.91/5.17  tff(f_151, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 12.91/5.17  tff(f_71, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 12.91/5.17  tff(f_44, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 12.91/5.17  tff(f_62, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 12.91/5.17  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.91/5.17  tff(c_130, plain, (k1_xboole_0='#skF_14' | k1_xboole_0!='#skF_15'), inference(cnfTransformation, [status(thm)], [f_225])).
% 12.91/5.17  tff(c_151, plain, (k1_xboole_0!='#skF_15'), inference(splitLeft, [status(thm)], [c_130])).
% 12.91/5.17  tff(c_128, plain, (~r2_hidden('#skF_17', k5_partfun1('#skF_14', '#skF_15', '#skF_16'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 12.91/5.17  tff(c_142, plain, (v1_funct_1('#skF_16')), inference(cnfTransformation, [status(thm)], [f_225])).
% 12.91/5.17  tff(c_132, plain, (r1_partfun1('#skF_16', '#skF_17')), inference(cnfTransformation, [status(thm)], [f_225])).
% 12.91/5.17  tff(c_140, plain, (m1_subset_1('#skF_16', k1_zfmisc_1(k2_zfmisc_1('#skF_14', '#skF_15')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 12.91/5.17  tff(c_138, plain, (v1_funct_1('#skF_17')), inference(cnfTransformation, [status(thm)], [f_225])).
% 12.91/5.17  tff(c_134, plain, (m1_subset_1('#skF_17', k1_zfmisc_1(k2_zfmisc_1('#skF_14', '#skF_15')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 12.91/5.17  tff(c_368, plain, (![C_159, B_160, A_161]: (v1_xboole_0(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(B_160, A_161))) | ~v1_xboole_0(A_161))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.91/5.17  tff(c_375, plain, (v1_xboole_0('#skF_17') | ~v1_xboole_0('#skF_15')), inference(resolution, [status(thm)], [c_134, c_368])).
% 12.91/5.17  tff(c_389, plain, (~v1_xboole_0('#skF_15')), inference(splitLeft, [status(thm)], [c_375])).
% 12.91/5.17  tff(c_136, plain, (v1_funct_2('#skF_17', '#skF_14', '#skF_15')), inference(cnfTransformation, [status(thm)], [f_225])).
% 12.91/5.17  tff(c_5700, plain, (![C_391, A_392, B_393]: (v1_partfun1(C_391, A_392) | ~v1_funct_2(C_391, A_392, B_393) | ~v1_funct_1(C_391) | ~m1_subset_1(C_391, k1_zfmisc_1(k2_zfmisc_1(A_392, B_393))) | v1_xboole_0(B_393))), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.91/5.17  tff(c_5707, plain, (v1_partfun1('#skF_17', '#skF_14') | ~v1_funct_2('#skF_17', '#skF_14', '#skF_15') | ~v1_funct_1('#skF_17') | v1_xboole_0('#skF_15')), inference(resolution, [status(thm)], [c_134, c_5700])).
% 12.91/5.17  tff(c_5714, plain, (v1_partfun1('#skF_17', '#skF_14') | v1_xboole_0('#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_136, c_5707])).
% 12.91/5.17  tff(c_5715, plain, (v1_partfun1('#skF_17', '#skF_14')), inference(negUnitSimplification, [status(thm)], [c_389, c_5714])).
% 12.91/5.17  tff(c_16916, plain, (![F_632, A_633, B_634, C_635]: (r2_hidden(F_632, k5_partfun1(A_633, B_634, C_635)) | ~r1_partfun1(C_635, F_632) | ~v1_partfun1(F_632, A_633) | ~m1_subset_1(F_632, k1_zfmisc_1(k2_zfmisc_1(A_633, B_634))) | ~v1_funct_1(F_632) | ~m1_subset_1(C_635, k1_zfmisc_1(k2_zfmisc_1(A_633, B_634))) | ~v1_funct_1(C_635))), inference(cnfTransformation, [status(thm)], [f_204])).
% 12.91/5.17  tff(c_16921, plain, (![C_635]: (r2_hidden('#skF_17', k5_partfun1('#skF_14', '#skF_15', C_635)) | ~r1_partfun1(C_635, '#skF_17') | ~v1_partfun1('#skF_17', '#skF_14') | ~v1_funct_1('#skF_17') | ~m1_subset_1(C_635, k1_zfmisc_1(k2_zfmisc_1('#skF_14', '#skF_15'))) | ~v1_funct_1(C_635))), inference(resolution, [status(thm)], [c_134, c_16916])).
% 12.91/5.17  tff(c_17242, plain, (![C_645]: (r2_hidden('#skF_17', k5_partfun1('#skF_14', '#skF_15', C_645)) | ~r1_partfun1(C_645, '#skF_17') | ~m1_subset_1(C_645, k1_zfmisc_1(k2_zfmisc_1('#skF_14', '#skF_15'))) | ~v1_funct_1(C_645))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_5715, c_16921])).
% 12.91/5.17  tff(c_17252, plain, (r2_hidden('#skF_17', k5_partfun1('#skF_14', '#skF_15', '#skF_16')) | ~r1_partfun1('#skF_16', '#skF_17') | ~v1_funct_1('#skF_16')), inference(resolution, [status(thm)], [c_140, c_17242])).
% 12.91/5.17  tff(c_17259, plain, (r2_hidden('#skF_17', k5_partfun1('#skF_14', '#skF_15', '#skF_16'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_132, c_17252])).
% 12.91/5.17  tff(c_17261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_17259])).
% 12.91/5.17  tff(c_17263, plain, (v1_xboole_0('#skF_15')), inference(splitRight, [status(thm)], [c_375])).
% 12.91/5.17  tff(c_34, plain, (![A_18]: (k1_xboole_0=A_18 | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.91/5.17  tff(c_17280, plain, (k1_xboole_0='#skF_15'), inference(resolution, [status(thm)], [c_17263, c_34])).
% 12.91/5.17  tff(c_17286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_17280])).
% 12.91/5.17  tff(c_17287, plain, (k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_130])).
% 12.91/5.17  tff(c_17288, plain, (k1_xboole_0='#skF_15'), inference(splitRight, [status(thm)], [c_130])).
% 12.91/5.17  tff(c_17295, plain, ('#skF_15'='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_17287, c_17288])).
% 12.91/5.17  tff(c_17332, plain, (m1_subset_1('#skF_17', k1_zfmisc_1(k2_zfmisc_1('#skF_14', '#skF_14')))), inference(demodulation, [status(thm), theory('equality')], [c_17295, c_134])).
% 12.91/5.17  tff(c_17399, plain, (![C_674, A_675, B_676]: (v1_relat_1(C_674) | ~m1_subset_1(C_674, k1_zfmisc_1(k2_zfmisc_1(A_675, B_676))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.91/5.17  tff(c_17406, plain, (v1_relat_1('#skF_17')), inference(resolution, [status(thm)], [c_17332, c_17399])).
% 12.91/5.17  tff(c_44, plain, (![A_26]: (k7_relat_1(A_26, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.91/5.17  tff(c_17322, plain, (![A_26]: (k7_relat_1(A_26, '#skF_14')='#skF_14' | ~v1_relat_1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_17287, c_17287, c_44])).
% 12.91/5.17  tff(c_17411, plain, (k7_relat_1('#skF_17', '#skF_14')='#skF_14'), inference(resolution, [status(thm)], [c_17406, c_17322])).
% 12.91/5.17  tff(c_42, plain, (![A_24, B_25]: (v1_relat_1(k7_relat_1(A_24, B_25)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.91/5.17  tff(c_17419, plain, (v1_relat_1('#skF_14') | ~v1_relat_1('#skF_17')), inference(superposition, [status(thm), theory('equality')], [c_17411, c_42])).
% 12.91/5.17  tff(c_17423, plain, (v1_relat_1('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_17406, c_17419])).
% 12.91/5.17  tff(c_50, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.91/5.17  tff(c_17290, plain, (k1_relat_1('#skF_14')='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_17287, c_17287, c_50])).
% 12.91/5.17  tff(c_46, plain, (![A_27]: (k7_relat_1(k1_xboole_0, A_27)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.91/5.17  tff(c_17309, plain, (![A_27]: (k7_relat_1('#skF_14', A_27)='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_17287, c_17287, c_46])).
% 12.91/5.17  tff(c_17487, plain, (![B_684, A_685]: (k3_xboole_0(k1_relat_1(B_684), A_685)=k1_relat_1(k7_relat_1(B_684, A_685)) | ~v1_relat_1(B_684))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.91/5.17  tff(c_17502, plain, (![A_685]: (k1_relat_1(k7_relat_1('#skF_14', A_685))=k3_xboole_0('#skF_14', A_685) | ~v1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_17290, c_17487])).
% 12.91/5.17  tff(c_17507, plain, (![A_686]: (k3_xboole_0('#skF_14', A_686)='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_17423, c_17290, c_17309, c_17502])).
% 12.91/5.17  tff(c_8, plain, (![D_10, B_6, A_5]: (r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.91/5.17  tff(c_17520, plain, (![D_687, A_688]: (r2_hidden(D_687, A_688) | ~r2_hidden(D_687, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_17507, c_8])).
% 12.91/5.17  tff(c_17532, plain, (![A_688]: (r2_hidden('#skF_1'('#skF_14'), A_688) | v1_xboole_0('#skF_14'))), inference(resolution, [status(thm)], [c_4, c_17520])).
% 12.91/5.17  tff(c_17533, plain, (v1_xboole_0('#skF_14')), inference(splitLeft, [status(thm)], [c_17532])).
% 12.91/5.17  tff(c_17319, plain, (m1_subset_1('#skF_16', k1_zfmisc_1(k2_zfmisc_1('#skF_14', '#skF_14')))), inference(demodulation, [status(thm), theory('equality')], [c_17295, c_140])).
% 12.91/5.17  tff(c_17534, plain, (![C_689, B_690, A_691]: (v1_xboole_0(C_689) | ~m1_subset_1(C_689, k1_zfmisc_1(k2_zfmisc_1(B_690, A_691))) | ~v1_xboole_0(A_691))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.91/5.17  tff(c_17542, plain, (v1_xboole_0('#skF_16') | ~v1_xboole_0('#skF_14')), inference(resolution, [status(thm)], [c_17319, c_17534])).
% 12.91/5.17  tff(c_17590, plain, (v1_xboole_0('#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_17533, c_17542])).
% 12.91/5.17  tff(c_17317, plain, (![A_18]: (A_18='#skF_14' | ~v1_xboole_0(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_17287, c_34])).
% 12.91/5.17  tff(c_17600, plain, ('#skF_16'='#skF_14'), inference(resolution, [status(thm)], [c_17590, c_17317])).
% 12.91/5.17  tff(c_17541, plain, (v1_xboole_0('#skF_17') | ~v1_xboole_0('#skF_14')), inference(resolution, [status(thm)], [c_17332, c_17534])).
% 12.91/5.17  tff(c_17556, plain, (v1_xboole_0('#skF_17')), inference(demodulation, [status(thm), theory('equality')], [c_17533, c_17541])).
% 12.91/5.17  tff(c_17566, plain, ('#skF_17'='#skF_14'), inference(resolution, [status(thm)], [c_17556, c_17317])).
% 12.91/5.17  tff(c_17321, plain, (~r2_hidden('#skF_17', k5_partfun1('#skF_14', '#skF_14', '#skF_16'))), inference(demodulation, [status(thm), theory('equality')], [c_17295, c_128])).
% 12.91/5.17  tff(c_17571, plain, (~r2_hidden('#skF_14', k5_partfun1('#skF_14', '#skF_14', '#skF_16'))), inference(demodulation, [status(thm), theory('equality')], [c_17566, c_17321])).
% 12.91/5.17  tff(c_17683, plain, (~r2_hidden('#skF_14', k5_partfun1('#skF_14', '#skF_14', '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_17600, c_17571])).
% 12.91/5.17  tff(c_17574, plain, (v1_funct_1('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_17566, c_138])).
% 12.91/5.17  tff(c_17573, plain, (r1_partfun1('#skF_16', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_17566, c_132])).
% 12.91/5.17  tff(c_17603, plain, (r1_partfun1('#skF_14', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_17600, c_17573])).
% 12.91/5.17  tff(c_17606, plain, (m1_subset_1('#skF_14', k1_zfmisc_1(k2_zfmisc_1('#skF_14', '#skF_14')))), inference(demodulation, [status(thm), theory('equality')], [c_17600, c_17319])).
% 12.91/5.17  tff(c_17582, plain, (![C_692, A_693, B_694]: (v1_partfun1(C_692, A_693) | ~m1_subset_1(C_692, k1_zfmisc_1(k2_zfmisc_1(A_693, B_694))) | ~v1_xboole_0(A_693))), inference(cnfTransformation, [status(thm)], [f_151])).
% 12.91/5.17  tff(c_17585, plain, (v1_partfun1('#skF_16', '#skF_14') | ~v1_xboole_0('#skF_14')), inference(resolution, [status(thm)], [c_17319, c_17582])).
% 12.91/5.17  tff(c_17588, plain, (v1_partfun1('#skF_16', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_17533, c_17585])).
% 12.91/5.17  tff(c_17602, plain, (v1_partfun1('#skF_14', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_17600, c_17588])).
% 12.91/5.17  tff(c_41006, plain, (![F_1318, A_1319, B_1320, C_1321]: (r2_hidden(F_1318, k5_partfun1(A_1319, B_1320, C_1321)) | ~r1_partfun1(C_1321, F_1318) | ~v1_partfun1(F_1318, A_1319) | ~m1_subset_1(F_1318, k1_zfmisc_1(k2_zfmisc_1(A_1319, B_1320))) | ~v1_funct_1(F_1318) | ~m1_subset_1(C_1321, k1_zfmisc_1(k2_zfmisc_1(A_1319, B_1320))) | ~v1_funct_1(C_1321))), inference(cnfTransformation, [status(thm)], [f_204])).
% 12.91/5.17  tff(c_41008, plain, (![C_1321]: (r2_hidden('#skF_14', k5_partfun1('#skF_14', '#skF_14', C_1321)) | ~r1_partfun1(C_1321, '#skF_14') | ~v1_partfun1('#skF_14', '#skF_14') | ~v1_funct_1('#skF_14') | ~m1_subset_1(C_1321, k1_zfmisc_1(k2_zfmisc_1('#skF_14', '#skF_14'))) | ~v1_funct_1(C_1321))), inference(resolution, [status(thm)], [c_17606, c_41006])).
% 12.91/5.17  tff(c_41886, plain, (![C_1328]: (r2_hidden('#skF_14', k5_partfun1('#skF_14', '#skF_14', C_1328)) | ~r1_partfun1(C_1328, '#skF_14') | ~m1_subset_1(C_1328, k1_zfmisc_1(k2_zfmisc_1('#skF_14', '#skF_14'))) | ~v1_funct_1(C_1328))), inference(demodulation, [status(thm), theory('equality')], [c_17574, c_17602, c_41008])).
% 12.91/5.17  tff(c_41889, plain, (r2_hidden('#skF_14', k5_partfun1('#skF_14', '#skF_14', '#skF_14')) | ~r1_partfun1('#skF_14', '#skF_14') | ~v1_funct_1('#skF_14')), inference(resolution, [status(thm)], [c_17606, c_41886])).
% 12.91/5.17  tff(c_41896, plain, (r2_hidden('#skF_14', k5_partfun1('#skF_14', '#skF_14', '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_17574, c_17603, c_41889])).
% 12.91/5.17  tff(c_41898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17683, c_41896])).
% 12.91/5.17  tff(c_41901, plain, (![A_1329]: (r2_hidden('#skF_1'('#skF_14'), A_1329))), inference(splitRight, [status(thm)], [c_17532])).
% 12.91/5.17  tff(c_36, plain, (![B_20, A_19]: (~v1_xboole_0(B_20) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.91/5.17  tff(c_41922, plain, (![A_1329]: (~v1_xboole_0(A_1329))), inference(resolution, [status(thm)], [c_41901, c_36])).
% 12.91/5.17  tff(c_41925, plain, (![A_1331]: (r2_hidden('#skF_1'(A_1331), A_1331))), inference(negUnitSimplification, [status(thm)], [c_41922, c_4])).
% 12.91/5.17  tff(c_10, plain, (![D_10, A_5, B_6]: (r2_hidden(D_10, A_5) | ~r2_hidden(D_10, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.91/5.17  tff(c_41941, plain, (![A_1332, B_1333]: (r2_hidden('#skF_1'(k3_xboole_0(A_1332, B_1333)), A_1332))), inference(resolution, [status(thm)], [c_41925, c_10])).
% 12.91/5.17  tff(c_42013, plain, (![A_1338, B_1339, B_1340]: (r2_hidden('#skF_1'(k3_xboole_0(k3_xboole_0(A_1338, B_1339), B_1340)), B_1339))), inference(resolution, [status(thm)], [c_41941, c_8])).
% 12.91/5.17  tff(c_17515, plain, (![D_10, A_686]: (r2_hidden(D_10, A_686) | ~r2_hidden(D_10, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_17507, c_8])).
% 12.91/5.17  tff(c_42031, plain, (![A_1338, B_1340, A_686]: (r2_hidden('#skF_1'(k3_xboole_0(k3_xboole_0(A_1338, '#skF_14'), B_1340)), A_686))), inference(resolution, [status(thm)], [c_42013, c_17515])).
% 12.91/5.17  tff(c_26, plain, (![A_11, B_12]: (r1_xboole_0(A_11, B_12) | k3_xboole_0(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.91/5.17  tff(c_17338, plain, (![A_11, B_12]: (r1_xboole_0(A_11, B_12) | k3_xboole_0(A_11, B_12)!='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_17287, c_26])).
% 12.91/5.17  tff(c_17477, plain, (![A_681, B_682, C_683]: (~r1_xboole_0(A_681, B_682) | ~r2_hidden(C_683, B_682) | ~r2_hidden(C_683, A_681))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.91/5.17  tff(c_42304, plain, (![C_1368, B_1369, A_1370]: (~r2_hidden(C_1368, B_1369) | ~r2_hidden(C_1368, A_1370) | k3_xboole_0(A_1370, B_1369)!='#skF_14')), inference(resolution, [status(thm)], [c_17338, c_17477])).
% 12.91/5.17  tff(c_42312, plain, (![A_1338, B_1340, A_1370, A_686]: (~r2_hidden('#skF_1'(k3_xboole_0(k3_xboole_0(A_1338, '#skF_14'), B_1340)), A_1370) | k3_xboole_0(A_1370, A_686)!='#skF_14')), inference(resolution, [status(thm)], [c_42031, c_42304])).
% 12.91/5.17  tff(c_42346, plain, (![A_1370, A_686]: (k3_xboole_0(A_1370, A_686)!='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_42031, c_42312])).
% 12.91/5.17  tff(c_17506, plain, (![A_685]: (k3_xboole_0('#skF_14', A_685)='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_17423, c_17290, c_17309, c_17502])).
% 12.91/5.17  tff(c_42369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42346, c_17506])).
% 12.91/5.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.91/5.17  
% 12.91/5.17  Inference rules
% 12.91/5.17  ----------------------
% 12.91/5.17  #Ref     : 0
% 12.91/5.17  #Sup     : 11156
% 12.91/5.17  #Fact    : 0
% 12.91/5.17  #Define  : 0
% 12.91/5.17  #Split   : 19
% 12.91/5.17  #Chain   : 0
% 12.91/5.17  #Close   : 0
% 12.91/5.17  
% 12.91/5.17  Ordering : KBO
% 12.91/5.17  
% 12.91/5.17  Simplification rules
% 12.91/5.17  ----------------------
% 12.91/5.17  #Subsume      : 3068
% 12.91/5.17  #Demod        : 7577
% 12.91/5.17  #Tautology    : 5168
% 12.91/5.17  #SimpNegUnit  : 182
% 12.91/5.17  #BackRed      : 89
% 12.91/5.17  
% 12.91/5.17  #Partial instantiations: 0
% 12.91/5.17  #Strategies tried      : 1
% 12.91/5.17  
% 12.91/5.17  Timing (in seconds)
% 12.91/5.17  ----------------------
% 12.91/5.18  Preprocessing        : 0.39
% 12.91/5.18  Parsing              : 0.19
% 12.91/5.18  CNF conversion       : 0.04
% 12.91/5.18  Main loop            : 3.99
% 12.91/5.18  Inferencing          : 0.99
% 12.91/5.18  Reduction            : 1.12
% 12.91/5.18  Demodulation         : 0.81
% 12.91/5.18  BG Simplification    : 0.12
% 12.91/5.18  Subsumption          : 1.49
% 12.91/5.18  Abstraction          : 0.17
% 12.91/5.18  MUC search           : 0.00
% 12.91/5.18  Cooper               : 0.00
% 12.91/5.18  Total                : 4.43
% 12.91/5.18  Index Insertion      : 0.00
% 12.91/5.18  Index Deletion       : 0.00
% 12.91/5.18  Index Matching       : 0.00
% 12.91/5.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
