%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:34 EST 2020

% Result     : Theorem 21.54s
% Output     : CNFRefutation 21.78s
% Verified   : 
% Statistics : Number of formulae       :  251 (2632 expanded)
%              Number of leaves         :   43 ( 811 expanded)
%              Depth                    :   15
%              Number of atoms          :  442 (7572 expanded)
%              Number of equality atoms :  102 (2412 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
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

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_130,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_142,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_67,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_66,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_96,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_104,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_96])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_84,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_67404,plain,(
    ! [A_1701,B_1702,C_1703] :
      ( k1_relset_1(A_1701,B_1702,C_1703) = k1_relat_1(C_1703)
      | ~ m1_subset_1(C_1703,k1_zfmisc_1(k2_zfmisc_1(A_1701,B_1702))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_67416,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_67404])).

tff(c_68908,plain,(
    ! [B_1791,A_1792,C_1793] :
      ( k1_xboole_0 = B_1791
      | k1_relset_1(A_1792,B_1791,C_1793) = A_1792
      | ~ v1_funct_2(C_1793,A_1792,B_1791)
      | ~ m1_subset_1(C_1793,k1_zfmisc_1(k2_zfmisc_1(A_1792,B_1791))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_68917,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_68908])).

tff(c_68927,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_67416,c_68917])).

tff(c_68928,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_68927])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k7_relat_1(B_16,A_15)) = A_15
      | ~ r1_tarski(A_15,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_68951,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68928,c_24])).

tff(c_68963,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_68951])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_68700,plain,(
    ! [A_1778,B_1779,C_1780,D_1781] :
      ( k2_partfun1(A_1778,B_1779,C_1780,D_1781) = k7_relat_1(C_1780,D_1781)
      | ~ m1_subset_1(C_1780,k1_zfmisc_1(k2_zfmisc_1(A_1778,B_1779)))
      | ~ v1_funct_1(C_1780) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_68706,plain,(
    ! [D_1781] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_1781) = k7_relat_1('#skF_4',D_1781)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_68700])).

tff(c_68716,plain,(
    ! [D_1781] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_1781) = k7_relat_1('#skF_4',D_1781) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68706])).

tff(c_1057,plain,(
    ! [C_154,A_155,B_156] :
      ( v4_relat_1(C_154,A_155)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1065,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_1057])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1069,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1065,c_18])).

tff(c_1072,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1069])).

tff(c_1084,plain,(
    ! [B_158,A_159] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_158,A_159)),k2_relat_1(B_158))
      | ~ v1_relat_1(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1090,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1072,c_1084])).

tff(c_1096,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1090])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( v5_relat_1(B_12,A_11)
      | ~ r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1113,plain,
    ( v5_relat_1('#skF_4',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1096,c_14])).

tff(c_1116,plain,(
    v5_relat_1('#skF_4',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1113])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_18,A_17)),k2_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1131,plain,(
    ! [A_164,C_165,B_166] :
      ( r1_tarski(A_164,C_165)
      | ~ r1_tarski(B_166,C_165)
      | ~ r1_tarski(A_164,B_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1377,plain,(
    ! [A_199,A_200,B_201] :
      ( r1_tarski(A_199,A_200)
      | ~ r1_tarski(A_199,k2_relat_1(B_201))
      | ~ v5_relat_1(B_201,A_200)
      | ~ v1_relat_1(B_201) ) ),
    inference(resolution,[status(thm)],[c_16,c_1131])).

tff(c_1388,plain,(
    ! [A_200] :
      ( r1_tarski(k2_relat_1('#skF_4'),A_200)
      | ~ v5_relat_1('#skF_4',A_200)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1096,c_1377])).

tff(c_1403,plain,(
    ! [A_202] :
      ( r1_tarski(k2_relat_1('#skF_4'),A_202)
      | ~ v5_relat_1('#skF_4',A_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1388])).

tff(c_6,plain,(
    ! [A_2,C_4,B_3] :
      ( r1_tarski(A_2,C_4)
      | ~ r1_tarski(B_3,C_4)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4786,plain,(
    ! [A_372,A_373] :
      ( r1_tarski(A_372,A_373)
      | ~ r1_tarski(A_372,k2_relat_1('#skF_4'))
      | ~ v5_relat_1('#skF_4',A_373) ) ),
    inference(resolution,[status(thm)],[c_1403,c_6])).

tff(c_4803,plain,(
    ! [A_17,A_373] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_17)),A_373)
      | ~ v5_relat_1('#skF_4',A_373)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_4786])).

tff(c_4814,plain,(
    ! [A_17,A_373] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_17)),A_373)
      | ~ v5_relat_1('#skF_4',A_373) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_4803])).

tff(c_1045,plain,(
    ! [C_150,B_151,A_152] :
      ( v5_relat_1(C_150,B_151)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_152,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1053,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_1045])).

tff(c_1143,plain,(
    ! [A_164,A_11,B_12] :
      ( r1_tarski(A_164,A_11)
      | ~ r1_tarski(A_164,k2_relat_1(B_12))
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_1131])).

tff(c_5244,plain,(
    ! [A_401,B_402] :
      ( r1_tarski(k2_relat_1('#skF_4'),A_401)
      | ~ v5_relat_1(B_402,A_401)
      | ~ v1_relat_1(B_402)
      | ~ v5_relat_1('#skF_4',k2_relat_1(B_402)) ) ),
    inference(resolution,[status(thm)],[c_1403,c_1143])).

tff(c_5254,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4')
    | ~ v5_relat_1('#skF_4',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1053,c_5244])).

tff(c_5265,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1116,c_104,c_5254])).

tff(c_5290,plain,(
    ! [A_411] :
      ( r1_tarski(A_411,'#skF_2')
      | ~ r1_tarski(A_411,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_5265,c_6])).

tff(c_5302,plain,(
    ! [A_17] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_17)),'#skF_2')
      | ~ v5_relat_1('#skF_4',k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4814,c_5290])).

tff(c_5330,plain,(
    ! [A_17] : r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_17)),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1116,c_5302])).

tff(c_6278,plain,(
    ! [A_462,B_463,C_464,D_465] :
      ( k2_partfun1(A_462,B_463,C_464,D_465) = k7_relat_1(C_464,D_465)
      | ~ m1_subset_1(C_464,k1_zfmisc_1(k2_zfmisc_1(A_462,B_463)))
      | ~ v1_funct_1(C_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_6282,plain,(
    ! [D_465] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_465) = k7_relat_1('#skF_4',D_465)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_6278])).

tff(c_6289,plain,(
    ! [D_465] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_465) = k7_relat_1('#skF_4',D_465) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6282])).

tff(c_7441,plain,(
    ! [A_513,B_514,C_515,D_516] :
      ( m1_subset_1(k2_partfun1(A_513,B_514,C_515,D_516),k1_zfmisc_1(k2_zfmisc_1(A_513,B_514)))
      | ~ m1_subset_1(C_515,k1_zfmisc_1(k2_zfmisc_1(A_513,B_514)))
      | ~ v1_funct_1(C_515) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_7483,plain,(
    ! [D_465] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_465),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6289,c_7441])).

tff(c_7540,plain,(
    ! [D_518] : m1_subset_1(k7_relat_1('#skF_4',D_518),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_7483])).

tff(c_28,plain,(
    ! [C_21,A_19,B_20] :
      ( v1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_7593,plain,(
    ! [D_518] : v1_relat_1(k7_relat_1('#skF_4',D_518)) ),
    inference(resolution,[status(thm)],[c_7540,c_28])).

tff(c_5266,plain,(
    ! [A_403,B_404,C_405,D_406] :
      ( v1_funct_1(k2_partfun1(A_403,B_404,C_405,D_406))
      | ~ m1_subset_1(C_405,k1_zfmisc_1(k2_zfmisc_1(A_403,B_404)))
      | ~ v1_funct_1(C_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_5268,plain,(
    ! [D_406] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_406))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_5266])).

tff(c_5274,plain,(
    ! [D_406] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_406)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5268])).

tff(c_6302,plain,(
    ! [D_406] : v1_funct_1(k7_relat_1('#skF_4',D_406)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6289,c_5274])).

tff(c_1337,plain,(
    ! [A_192,B_193,C_194] :
      ( k1_relset_1(A_192,B_193,C_194) = k1_relat_1(C_194)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1345,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1337])).

tff(c_7186,plain,(
    ! [B_504,A_505,C_506] :
      ( k1_xboole_0 = B_504
      | k1_relset_1(A_505,B_504,C_506) = A_505
      | ~ v1_funct_2(C_506,A_505,B_504)
      | ~ m1_subset_1(C_506,k1_zfmisc_1(k2_zfmisc_1(A_505,B_504))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_7192,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_7186])).

tff(c_7200,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1345,c_7192])).

tff(c_7201,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_7200])).

tff(c_7224,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7201,c_24])).

tff(c_7300,plain,(
    ! [A_511] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_511)) = A_511
      | ~ r1_tarski(A_511,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_7224])).

tff(c_56,plain,(
    ! [B_44,A_43] :
      ( m1_subset_1(B_44,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_44),A_43)))
      | ~ r1_tarski(k2_relat_1(B_44),A_43)
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_7314,plain,(
    ! [A_511,A_43] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_511),k1_zfmisc_1(k2_zfmisc_1(A_511,A_43)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_511)),A_43)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_511))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_511))
      | ~ r1_tarski(A_511,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7300,c_56])).

tff(c_7364,plain,(
    ! [A_511,A_43] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_511),k1_zfmisc_1(k2_zfmisc_1(A_511,A_43)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_511)),A_43)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_511))
      | ~ r1_tarski(A_511,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6302,c_7314])).

tff(c_67038,plain,(
    ! [A_1669,A_1670] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_1669),k1_zfmisc_1(k2_zfmisc_1(A_1669,A_1670)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_1669)),A_1670)
      | ~ r1_tarski(A_1669,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7593,c_7364])).

tff(c_1030,plain,(
    ! [A_146,B_147,C_148,D_149] :
      ( v1_funct_1(k2_partfun1(A_146,B_147,C_148,D_149))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147)))
      | ~ v1_funct_1(C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1032,plain,(
    ! [D_149] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_149))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_1030])).

tff(c_1038,plain,(
    ! [D_149] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_149)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1032])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_114,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_1042,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_114])).

tff(c_1043,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1117,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1043])).

tff(c_6303,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6289,c_1117])).

tff(c_67088,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_67038,c_6303])).

tff(c_67188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5330,c_67088])).

tff(c_67190,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1043])).

tff(c_67415,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_67190,c_67404])).

tff(c_68727,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68716,c_68716,c_67415])).

tff(c_67189,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1043])).

tff(c_68733,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68716,c_67189])).

tff(c_68732,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68716,c_67190])).

tff(c_68808,plain,(
    ! [B_1784,C_1785,A_1786] :
      ( k1_xboole_0 = B_1784
      | v1_funct_2(C_1785,A_1786,B_1784)
      | k1_relset_1(A_1786,B_1784,C_1785) != A_1786
      | ~ m1_subset_1(C_1785,k1_zfmisc_1(k2_zfmisc_1(A_1786,B_1784))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_68811,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_68732,c_68808])).

tff(c_68824,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_68733,c_84,c_68811])).

tff(c_69395,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68727,c_68824])).

tff(c_69402,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_68963,c_69395])).

tff(c_69406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_69402])).

tff(c_69407,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_69408,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_69417,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69407,c_69408])).

tff(c_69423,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69417,c_68])).

tff(c_69446,plain,(
    ! [C_1817,A_1818,B_1819] :
      ( v1_relat_1(C_1817)
      | ~ m1_subset_1(C_1817,k1_zfmisc_1(k2_zfmisc_1(A_1818,B_1819))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_69455,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_69423,c_69446])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_69412,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69407,c_2])).

tff(c_71619,plain,(
    ! [C_2073,A_2074,B_2075] :
      ( v1_xboole_0(C_2073)
      | ~ m1_subset_1(C_2073,k1_zfmisc_1(k2_zfmisc_1(A_2074,B_2075)))
      | ~ v1_xboole_0(A_2074) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_71629,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_69423,c_71619])).

tff(c_71635,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69412,c_71629])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_69433,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69407,c_4])).

tff(c_71642,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_71635,c_69433])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69409,plain,(
    ! [A_7] : m1_subset_1('#skF_1',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69407,c_10])).

tff(c_69454,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_69409,c_69446])).

tff(c_70077,plain,(
    ! [C_1902,B_1903,A_1904] :
      ( v5_relat_1(C_1902,B_1903)
      | ~ m1_subset_1(C_1902,k1_zfmisc_1(k2_zfmisc_1(A_1904,B_1903))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_70085,plain,(
    ! [B_1903] : v5_relat_1('#skF_1',B_1903) ),
    inference(resolution,[status(thm)],[c_69409,c_70077])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_69410,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69407,c_69407,c_20])).

tff(c_71441,plain,(
    ! [B_2051,A_2052] :
      ( r1_tarski(k2_relat_1(B_2051),A_2052)
      | ~ v5_relat_1(B_2051,A_2052)
      | ~ v1_relat_1(B_2051) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71453,plain,(
    ! [A_2052] :
      ( r1_tarski('#skF_1',A_2052)
      | ~ v5_relat_1('#skF_1',A_2052)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69410,c_71441])).

tff(c_71458,plain,(
    ! [A_2052] : r1_tarski('#skF_1',A_2052) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69454,c_70085,c_71453])).

tff(c_71651,plain,(
    ! [A_2052] : r1_tarski('#skF_4',A_2052) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71642,c_71458])).

tff(c_71668,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71642,c_71642,c_69410])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_69411,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69407,c_69407,c_22])).

tff(c_71669,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71642,c_71642,c_69411])).

tff(c_71880,plain,(
    ! [B_2094,A_2095] :
      ( v1_funct_2(B_2094,k1_relat_1(B_2094),A_2095)
      | ~ r1_tarski(k2_relat_1(B_2094),A_2095)
      | ~ v1_funct_1(B_2094)
      | ~ v1_relat_1(B_2094) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_71883,plain,(
    ! [A_2095] :
      ( v1_funct_2('#skF_4','#skF_4',A_2095)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_2095)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71669,c_71880])).

tff(c_71885,plain,(
    ! [A_2095] : v1_funct_2('#skF_4','#skF_4',A_2095) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69455,c_72,c_71651,c_71668,c_71883])).

tff(c_70049,plain,(
    ! [C_1896,A_1897,B_1898] :
      ( v4_relat_1(C_1896,A_1897)
      | ~ m1_subset_1(C_1896,k1_zfmisc_1(k2_zfmisc_1(A_1897,B_1898))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_70057,plain,(
    ! [A_1897] : v4_relat_1('#skF_1',A_1897) ),
    inference(resolution,[status(thm)],[c_69409,c_70049])).

tff(c_70060,plain,(
    ! [B_1900,A_1901] :
      ( k7_relat_1(B_1900,A_1901) = B_1900
      | ~ v4_relat_1(B_1900,A_1901)
      | ~ v1_relat_1(B_1900) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_70066,plain,(
    ! [A_1897] :
      ( k7_relat_1('#skF_1',A_1897) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70057,c_70060])).

tff(c_70072,plain,(
    ! [A_1897] : k7_relat_1('#skF_1',A_1897) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69454,c_70066])).

tff(c_71657,plain,(
    ! [A_1897] : k7_relat_1('#skF_4',A_1897) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71642,c_71642,c_70072])).

tff(c_71460,plain,(
    ! [A_2053] : r1_tarski('#skF_1',A_2053) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69454,c_70085,c_71453])).

tff(c_71470,plain,(
    ! [A_2054,A_2055] :
      ( r1_tarski(A_2054,A_2055)
      | ~ r1_tarski(A_2054,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_71460,c_6])).

tff(c_71482,plain,(
    ! [A_2055] : r1_tarski('#skF_3',A_2055) ),
    inference(resolution,[status(thm)],[c_66,c_71470])).

tff(c_71731,plain,(
    ! [B_2078,A_2079] :
      ( k1_relat_1(k7_relat_1(B_2078,A_2079)) = A_2079
      | ~ r1_tarski(A_2079,k1_relat_1(B_2078))
      | ~ v1_relat_1(B_2078) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_71841,plain,(
    ! [B_2091] :
      ( k1_relat_1(k7_relat_1(B_2091,'#skF_3')) = '#skF_3'
      | ~ v1_relat_1(B_2091) ) ),
    inference(resolution,[status(thm)],[c_71482,c_71731])).

tff(c_71854,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_71657,c_71841])).

tff(c_71858,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69455,c_71669,c_71854])).

tff(c_70329,plain,(
    ! [C_1940,A_1941,B_1942] :
      ( v1_xboole_0(C_1940)
      | ~ m1_subset_1(C_1940,k1_zfmisc_1(k2_zfmisc_1(A_1941,B_1942)))
      | ~ v1_xboole_0(A_1941) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_70336,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_69423,c_70329])).

tff(c_70341,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69412,c_70336])).

tff(c_70348,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_70341,c_69433])).

tff(c_70366,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70348,c_69409])).

tff(c_70356,plain,(
    ! [A_1897] : k7_relat_1('#skF_4',A_1897) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70348,c_70348,c_70072])).

tff(c_71349,plain,(
    ! [A_2039,B_2040,C_2041,D_2042] :
      ( k2_partfun1(A_2039,B_2040,C_2041,D_2042) = k7_relat_1(C_2041,D_2042)
      | ~ m1_subset_1(C_2041,k1_zfmisc_1(k2_zfmisc_1(A_2039,B_2040)))
      | ~ v1_funct_1(C_2041) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_71354,plain,(
    ! [A_2039,B_2040,D_2042] :
      ( k2_partfun1(A_2039,B_2040,'#skF_4',D_2042) = k7_relat_1('#skF_4',D_2042)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70366,c_71349])).

tff(c_71358,plain,(
    ! [A_2039,B_2040,D_2042] : k2_partfun1(A_2039,B_2040,'#skF_4',D_2042) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70356,c_71354])).

tff(c_70368,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70348,c_70348,c_69411])).

tff(c_70129,plain,(
    ! [B_1911,A_1912] :
      ( r1_tarski(k2_relat_1(B_1911),A_1912)
      | ~ v5_relat_1(B_1911,A_1912)
      | ~ v1_relat_1(B_1911) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_70135,plain,(
    ! [A_1912] :
      ( r1_tarski('#skF_1',A_1912)
      | ~ v5_relat_1('#skF_1',A_1912)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69410,c_70129])).

tff(c_70138,plain,(
    ! [A_1912] : r1_tarski('#skF_1',A_1912) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69454,c_70085,c_70135])).

tff(c_70141,plain,(
    ! [A_1914,C_1915,B_1916] :
      ( r1_tarski(A_1914,C_1915)
      | ~ r1_tarski(B_1916,C_1915)
      | ~ r1_tarski(A_1914,B_1916) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_70169,plain,(
    ! [A_1918,A_1919] :
      ( r1_tarski(A_1918,A_1919)
      | ~ r1_tarski(A_1918,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70138,c_70141])).

tff(c_70181,plain,(
    ! [A_1919] : r1_tarski('#skF_3',A_1919) ),
    inference(resolution,[status(thm)],[c_66,c_70169])).

tff(c_70435,plain,(
    ! [B_1945,A_1946] :
      ( k1_relat_1(k7_relat_1(B_1945,A_1946)) = A_1946
      | ~ r1_tarski(A_1946,k1_relat_1(B_1945))
      | ~ v1_relat_1(B_1945) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_70544,plain,(
    ! [B_1958] :
      ( k1_relat_1(k7_relat_1(B_1958,'#skF_3')) = '#skF_3'
      | ~ v1_relat_1(B_1958) ) ),
    inference(resolution,[status(thm)],[c_70181,c_70435])).

tff(c_70557,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_70356,c_70544])).

tff(c_70561,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69455,c_70368,c_70557])).

tff(c_69716,plain,(
    ! [C_1862,A_1863,B_1864] :
      ( v1_xboole_0(C_1862)
      | ~ m1_subset_1(C_1862,k1_zfmisc_1(k2_zfmisc_1(A_1863,B_1864)))
      | ~ v1_xboole_0(A_1863) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_69723,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_69423,c_69716])).

tff(c_69728,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69412,c_69723])).

tff(c_69735,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_69728,c_69433])).

tff(c_69751,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69735,c_69409])).

tff(c_70037,plain,(
    ! [A_1892,B_1893,C_1894,D_1895] :
      ( v1_funct_1(k2_partfun1(A_1892,B_1893,C_1894,D_1895))
      | ~ m1_subset_1(C_1894,k1_zfmisc_1(k2_zfmisc_1(A_1892,B_1893)))
      | ~ v1_funct_1(C_1894) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_70040,plain,(
    ! [A_1892,B_1893,D_1895] :
      ( v1_funct_1(k2_partfun1(A_1892,B_1893,'#skF_4',D_1895))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_69751,c_70037])).

tff(c_70043,plain,(
    ! [A_1892,B_1893,D_1895] : v1_funct_1(k2_partfun1(A_1892,B_1893,'#skF_4',D_1895)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70040])).

tff(c_69753,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69735,c_69735,c_69411])).

tff(c_69555,plain,(
    ! [C_1837,A_1838,B_1839] :
      ( v4_relat_1(C_1837,A_1838)
      | ~ m1_subset_1(C_1837,k1_zfmisc_1(k2_zfmisc_1(A_1838,B_1839))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_69563,plain,(
    ! [A_1838] : v4_relat_1('#skF_1',A_1838) ),
    inference(resolution,[status(thm)],[c_69409,c_69555])).

tff(c_69631,plain,(
    ! [B_1849,A_1850] :
      ( k7_relat_1(B_1849,A_1850) = B_1849
      | ~ v4_relat_1(B_1849,A_1850)
      | ~ v1_relat_1(B_1849) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_69637,plain,(
    ! [A_1838] :
      ( k7_relat_1('#skF_1',A_1838) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_69563,c_69631])).

tff(c_69643,plain,(
    ! [A_1838] : k7_relat_1('#skF_1',A_1838) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69454,c_69637])).

tff(c_69738,plain,(
    ! [A_1838] : k7_relat_1('#skF_4',A_1838) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69735,c_69735,c_69643])).

tff(c_69458,plain,(
    ! [C_1820,B_1821,A_1822] :
      ( v5_relat_1(C_1820,B_1821)
      | ~ m1_subset_1(C_1820,k1_zfmisc_1(k2_zfmisc_1(A_1822,B_1821))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_69466,plain,(
    ! [B_1821] : v5_relat_1('#skF_1',B_1821) ),
    inference(resolution,[status(thm)],[c_69409,c_69458])).

tff(c_69474,plain,(
    ! [B_1828,A_1829] :
      ( r1_tarski(k2_relat_1(B_1828),A_1829)
      | ~ v5_relat_1(B_1828,A_1829)
      | ~ v1_relat_1(B_1828) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_69483,plain,(
    ! [A_1829] :
      ( r1_tarski('#skF_1',A_1829)
      | ~ v5_relat_1('#skF_1',A_1829)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69410,c_69474])).

tff(c_69497,plain,(
    ! [A_1831] : r1_tarski('#skF_1',A_1831) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69454,c_69466,c_69483])).

tff(c_69508,plain,(
    ! [A_1832,A_1833] :
      ( r1_tarski(A_1832,A_1833)
      | ~ r1_tarski(A_1832,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_69497,c_6])).

tff(c_69523,plain,(
    ! [A_1833] : r1_tarski('#skF_3',A_1833) ),
    inference(resolution,[status(thm)],[c_66,c_69508])).

tff(c_69798,plain,(
    ! [B_1868,A_1869] :
      ( k1_relat_1(k7_relat_1(B_1868,A_1869)) = A_1869
      | ~ r1_tarski(A_1869,k1_relat_1(B_1868))
      | ~ v1_relat_1(B_1868) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_69977,plain,(
    ! [B_1887] :
      ( k1_relat_1(k7_relat_1(B_1887,'#skF_3')) = '#skF_3'
      | ~ v1_relat_1(B_1887) ) ),
    inference(resolution,[status(thm)],[c_69523,c_69798])).

tff(c_69993,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_69738,c_69977])).

tff(c_69997,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69455,c_69753,c_69993])).

tff(c_69456,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69417,c_69417,c_69417,c_69417,c_69417,c_62])).

tff(c_69457,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_69456])).

tff(c_69746,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69735,c_69735,c_69457])).

tff(c_69999,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69997,c_69746])).

tff(c_70046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70043,c_69999])).

tff(c_70047,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_69456])).

tff(c_70095,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_70047])).

tff(c_70349,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70348,c_70348,c_70348,c_70095])).

tff(c_70694,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70561,c_70561,c_70349])).

tff(c_71360,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71358,c_70694])).

tff(c_71364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70366,c_71360])).

tff(c_71366,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_70047])).

tff(c_71630,plain,
    ( v1_xboole_0(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_71366,c_71619])).

tff(c_71919,plain,(
    v1_xboole_0(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71635,c_71858,c_71858,c_71642,c_71642,c_71630])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_71641,plain,(
    ! [A_5] :
      ( A_5 = '#skF_4'
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_71635,c_8])).

tff(c_71925,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_71919,c_71641])).

tff(c_71365,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_70047])).

tff(c_71656,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71642,c_71642,c_71642,c_71365])).

tff(c_71950,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71885,c_71925,c_71858,c_71858,c_71656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.54/11.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.78/11.54  
% 21.78/11.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.78/11.54  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 21.78/11.54  
% 21.78/11.54  %Foreground sorts:
% 21.78/11.54  
% 21.78/11.54  
% 21.78/11.54  %Background operators:
% 21.78/11.54  
% 21.78/11.54  
% 21.78/11.54  %Foreground operators:
% 21.78/11.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 21.78/11.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.78/11.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.78/11.54  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 21.78/11.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.78/11.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.78/11.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 21.78/11.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 21.78/11.54  tff('#skF_2', type, '#skF_2': $i).
% 21.78/11.54  tff('#skF_3', type, '#skF_3': $i).
% 21.78/11.54  tff('#skF_1', type, '#skF_1': $i).
% 21.78/11.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 21.78/11.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 21.78/11.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.78/11.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.78/11.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 21.78/11.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 21.78/11.54  tff('#skF_4', type, '#skF_4': $i).
% 21.78/11.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.78/11.54  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 21.78/11.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 21.78/11.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 21.78/11.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 21.78/11.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.78/11.54  
% 21.78/11.57  tff(f_162, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 21.78/11.57  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 21.78/11.57  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 21.78/11.57  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 21.78/11.57  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 21.78/11.57  tff(f_130, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 21.78/11.57  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 21.78/11.57  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 21.78/11.57  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 21.78/11.57  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 21.78/11.57  tff(f_36, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 21.78/11.57  tff(f_124, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 21.78/11.57  tff(f_142, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 21.78/11.57  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 21.78/11.57  tff(f_94, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 21.78/11.57  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 21.78/11.57  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 21.78/11.57  tff(f_67, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 21.78/11.57  tff(f_44, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 21.78/11.57  tff(c_66, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 21.78/11.57  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 21.78/11.57  tff(c_96, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 21.78/11.57  tff(c_104, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_96])).
% 21.78/11.57  tff(c_64, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_162])).
% 21.78/11.57  tff(c_84, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_64])).
% 21.78/11.57  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 21.78/11.57  tff(c_67404, plain, (![A_1701, B_1702, C_1703]: (k1_relset_1(A_1701, B_1702, C_1703)=k1_relat_1(C_1703) | ~m1_subset_1(C_1703, k1_zfmisc_1(k2_zfmisc_1(A_1701, B_1702))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 21.78/11.57  tff(c_67416, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_67404])).
% 21.78/11.57  tff(c_68908, plain, (![B_1791, A_1792, C_1793]: (k1_xboole_0=B_1791 | k1_relset_1(A_1792, B_1791, C_1793)=A_1792 | ~v1_funct_2(C_1793, A_1792, B_1791) | ~m1_subset_1(C_1793, k1_zfmisc_1(k2_zfmisc_1(A_1792, B_1791))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 21.78/11.57  tff(c_68917, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_68908])).
% 21.78/11.57  tff(c_68927, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_67416, c_68917])).
% 21.78/11.57  tff(c_68928, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_84, c_68927])).
% 21.78/11.57  tff(c_24, plain, (![B_16, A_15]: (k1_relat_1(k7_relat_1(B_16, A_15))=A_15 | ~r1_tarski(A_15, k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_73])).
% 21.78/11.57  tff(c_68951, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_68928, c_24])).
% 21.78/11.57  tff(c_68963, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_68951])).
% 21.78/11.57  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 21.78/11.57  tff(c_68700, plain, (![A_1778, B_1779, C_1780, D_1781]: (k2_partfun1(A_1778, B_1779, C_1780, D_1781)=k7_relat_1(C_1780, D_1781) | ~m1_subset_1(C_1780, k1_zfmisc_1(k2_zfmisc_1(A_1778, B_1779))) | ~v1_funct_1(C_1780))), inference(cnfTransformation, [status(thm)], [f_130])).
% 21.78/11.57  tff(c_68706, plain, (![D_1781]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1781)=k7_relat_1('#skF_4', D_1781) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_68700])).
% 21.78/11.57  tff(c_68716, plain, (![D_1781]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1781)=k7_relat_1('#skF_4', D_1781))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68706])).
% 21.78/11.57  tff(c_1057, plain, (![C_154, A_155, B_156]: (v4_relat_1(C_154, A_155) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 21.78/11.57  tff(c_1065, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_1057])).
% 21.78/11.57  tff(c_18, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 21.78/11.57  tff(c_1069, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1065, c_18])).
% 21.78/11.57  tff(c_1072, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1069])).
% 21.78/11.57  tff(c_1084, plain, (![B_158, A_159]: (r1_tarski(k2_relat_1(k7_relat_1(B_158, A_159)), k2_relat_1(B_158)) | ~v1_relat_1(B_158))), inference(cnfTransformation, [status(thm)], [f_77])).
% 21.78/11.57  tff(c_1090, plain, (r1_tarski(k2_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1072, c_1084])).
% 21.78/11.57  tff(c_1096, plain, (r1_tarski(k2_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1090])).
% 21.78/11.57  tff(c_14, plain, (![B_12, A_11]: (v5_relat_1(B_12, A_11) | ~r1_tarski(k2_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.78/11.57  tff(c_1113, plain, (v5_relat_1('#skF_4', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1096, c_14])).
% 21.78/11.57  tff(c_1116, plain, (v5_relat_1('#skF_4', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1113])).
% 21.78/11.57  tff(c_26, plain, (![B_18, A_17]: (r1_tarski(k2_relat_1(k7_relat_1(B_18, A_17)), k2_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 21.78/11.57  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.78/11.57  tff(c_1131, plain, (![A_164, C_165, B_166]: (r1_tarski(A_164, C_165) | ~r1_tarski(B_166, C_165) | ~r1_tarski(A_164, B_166))), inference(cnfTransformation, [status(thm)], [f_36])).
% 21.78/11.57  tff(c_1377, plain, (![A_199, A_200, B_201]: (r1_tarski(A_199, A_200) | ~r1_tarski(A_199, k2_relat_1(B_201)) | ~v5_relat_1(B_201, A_200) | ~v1_relat_1(B_201))), inference(resolution, [status(thm)], [c_16, c_1131])).
% 21.78/11.57  tff(c_1388, plain, (![A_200]: (r1_tarski(k2_relat_1('#skF_4'), A_200) | ~v5_relat_1('#skF_4', A_200) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1096, c_1377])).
% 21.78/11.57  tff(c_1403, plain, (![A_202]: (r1_tarski(k2_relat_1('#skF_4'), A_202) | ~v5_relat_1('#skF_4', A_202))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1388])).
% 21.78/11.57  tff(c_6, plain, (![A_2, C_4, B_3]: (r1_tarski(A_2, C_4) | ~r1_tarski(B_3, C_4) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 21.78/11.57  tff(c_4786, plain, (![A_372, A_373]: (r1_tarski(A_372, A_373) | ~r1_tarski(A_372, k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', A_373))), inference(resolution, [status(thm)], [c_1403, c_6])).
% 21.78/11.57  tff(c_4803, plain, (![A_17, A_373]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_17)), A_373) | ~v5_relat_1('#skF_4', A_373) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_4786])).
% 21.78/11.57  tff(c_4814, plain, (![A_17, A_373]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_17)), A_373) | ~v5_relat_1('#skF_4', A_373))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_4803])).
% 21.78/11.57  tff(c_1045, plain, (![C_150, B_151, A_152]: (v5_relat_1(C_150, B_151) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_152, B_151))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 21.78/11.57  tff(c_1053, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_1045])).
% 21.78/11.57  tff(c_1143, plain, (![A_164, A_11, B_12]: (r1_tarski(A_164, A_11) | ~r1_tarski(A_164, k2_relat_1(B_12)) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(resolution, [status(thm)], [c_16, c_1131])).
% 21.78/11.57  tff(c_5244, plain, (![A_401, B_402]: (r1_tarski(k2_relat_1('#skF_4'), A_401) | ~v5_relat_1(B_402, A_401) | ~v1_relat_1(B_402) | ~v5_relat_1('#skF_4', k2_relat_1(B_402)))), inference(resolution, [status(thm)], [c_1403, c_1143])).
% 21.78/11.57  tff(c_5254, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4') | ~v5_relat_1('#skF_4', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1053, c_5244])).
% 21.78/11.57  tff(c_5265, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1116, c_104, c_5254])).
% 21.78/11.57  tff(c_5290, plain, (![A_411]: (r1_tarski(A_411, '#skF_2') | ~r1_tarski(A_411, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_5265, c_6])).
% 21.78/11.57  tff(c_5302, plain, (![A_17]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_17)), '#skF_2') | ~v5_relat_1('#skF_4', k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_4814, c_5290])).
% 21.78/11.57  tff(c_5330, plain, (![A_17]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_17)), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1116, c_5302])).
% 21.78/11.57  tff(c_6278, plain, (![A_462, B_463, C_464, D_465]: (k2_partfun1(A_462, B_463, C_464, D_465)=k7_relat_1(C_464, D_465) | ~m1_subset_1(C_464, k1_zfmisc_1(k2_zfmisc_1(A_462, B_463))) | ~v1_funct_1(C_464))), inference(cnfTransformation, [status(thm)], [f_130])).
% 21.78/11.57  tff(c_6282, plain, (![D_465]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_465)=k7_relat_1('#skF_4', D_465) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_6278])).
% 21.78/11.57  tff(c_6289, plain, (![D_465]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_465)=k7_relat_1('#skF_4', D_465))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6282])).
% 21.78/11.57  tff(c_7441, plain, (![A_513, B_514, C_515, D_516]: (m1_subset_1(k2_partfun1(A_513, B_514, C_515, D_516), k1_zfmisc_1(k2_zfmisc_1(A_513, B_514))) | ~m1_subset_1(C_515, k1_zfmisc_1(k2_zfmisc_1(A_513, B_514))) | ~v1_funct_1(C_515))), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.78/11.57  tff(c_7483, plain, (![D_465]: (m1_subset_1(k7_relat_1('#skF_4', D_465), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6289, c_7441])).
% 21.78/11.57  tff(c_7540, plain, (![D_518]: (m1_subset_1(k7_relat_1('#skF_4', D_518), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_7483])).
% 21.78/11.57  tff(c_28, plain, (![C_21, A_19, B_20]: (v1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 21.78/11.57  tff(c_7593, plain, (![D_518]: (v1_relat_1(k7_relat_1('#skF_4', D_518)))), inference(resolution, [status(thm)], [c_7540, c_28])).
% 21.78/11.57  tff(c_5266, plain, (![A_403, B_404, C_405, D_406]: (v1_funct_1(k2_partfun1(A_403, B_404, C_405, D_406)) | ~m1_subset_1(C_405, k1_zfmisc_1(k2_zfmisc_1(A_403, B_404))) | ~v1_funct_1(C_405))), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.78/11.57  tff(c_5268, plain, (![D_406]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_406)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_5266])).
% 21.78/11.57  tff(c_5274, plain, (![D_406]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_406)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_5268])).
% 21.78/11.57  tff(c_6302, plain, (![D_406]: (v1_funct_1(k7_relat_1('#skF_4', D_406)))), inference(demodulation, [status(thm), theory('equality')], [c_6289, c_5274])).
% 21.78/11.57  tff(c_1337, plain, (![A_192, B_193, C_194]: (k1_relset_1(A_192, B_193, C_194)=k1_relat_1(C_194) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 21.78/11.57  tff(c_1345, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_1337])).
% 21.78/11.57  tff(c_7186, plain, (![B_504, A_505, C_506]: (k1_xboole_0=B_504 | k1_relset_1(A_505, B_504, C_506)=A_505 | ~v1_funct_2(C_506, A_505, B_504) | ~m1_subset_1(C_506, k1_zfmisc_1(k2_zfmisc_1(A_505, B_504))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 21.78/11.57  tff(c_7192, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_7186])).
% 21.78/11.57  tff(c_7200, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1345, c_7192])).
% 21.78/11.57  tff(c_7201, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_84, c_7200])).
% 21.78/11.57  tff(c_7224, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7201, c_24])).
% 21.78/11.57  tff(c_7300, plain, (![A_511]: (k1_relat_1(k7_relat_1('#skF_4', A_511))=A_511 | ~r1_tarski(A_511, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_7224])).
% 21.78/11.57  tff(c_56, plain, (![B_44, A_43]: (m1_subset_1(B_44, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_44), A_43))) | ~r1_tarski(k2_relat_1(B_44), A_43) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_142])).
% 21.78/11.57  tff(c_7314, plain, (![A_511, A_43]: (m1_subset_1(k7_relat_1('#skF_4', A_511), k1_zfmisc_1(k2_zfmisc_1(A_511, A_43))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_511)), A_43) | ~v1_funct_1(k7_relat_1('#skF_4', A_511)) | ~v1_relat_1(k7_relat_1('#skF_4', A_511)) | ~r1_tarski(A_511, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7300, c_56])).
% 21.78/11.57  tff(c_7364, plain, (![A_511, A_43]: (m1_subset_1(k7_relat_1('#skF_4', A_511), k1_zfmisc_1(k2_zfmisc_1(A_511, A_43))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_511)), A_43) | ~v1_relat_1(k7_relat_1('#skF_4', A_511)) | ~r1_tarski(A_511, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6302, c_7314])).
% 21.78/11.57  tff(c_67038, plain, (![A_1669, A_1670]: (m1_subset_1(k7_relat_1('#skF_4', A_1669), k1_zfmisc_1(k2_zfmisc_1(A_1669, A_1670))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_1669)), A_1670) | ~r1_tarski(A_1669, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7593, c_7364])).
% 21.78/11.57  tff(c_1030, plain, (![A_146, B_147, C_148, D_149]: (v1_funct_1(k2_partfun1(A_146, B_147, C_148, D_149)) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))) | ~v1_funct_1(C_148))), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.78/11.57  tff(c_1032, plain, (![D_149]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_149)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_1030])).
% 21.78/11.57  tff(c_1038, plain, (![D_149]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_149)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1032])).
% 21.78/11.57  tff(c_62, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 21.78/11.57  tff(c_114, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 21.78/11.57  tff(c_1042, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1038, c_114])).
% 21.78/11.57  tff(c_1043, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_62])).
% 21.78/11.57  tff(c_1117, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1043])).
% 21.78/11.57  tff(c_6303, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6289, c_1117])).
% 21.78/11.57  tff(c_67088, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_67038, c_6303])).
% 21.78/11.57  tff(c_67188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_5330, c_67088])).
% 21.78/11.57  tff(c_67190, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_1043])).
% 21.78/11.57  tff(c_67415, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_67190, c_67404])).
% 21.78/11.57  tff(c_68727, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68716, c_68716, c_67415])).
% 21.78/11.57  tff(c_67189, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_1043])).
% 21.78/11.57  tff(c_68733, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68716, c_67189])).
% 21.78/11.57  tff(c_68732, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_68716, c_67190])).
% 21.78/11.57  tff(c_68808, plain, (![B_1784, C_1785, A_1786]: (k1_xboole_0=B_1784 | v1_funct_2(C_1785, A_1786, B_1784) | k1_relset_1(A_1786, B_1784, C_1785)!=A_1786 | ~m1_subset_1(C_1785, k1_zfmisc_1(k2_zfmisc_1(A_1786, B_1784))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 21.78/11.57  tff(c_68811, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_68732, c_68808])).
% 21.78/11.57  tff(c_68824, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_68733, c_84, c_68811])).
% 21.78/11.57  tff(c_69395, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68727, c_68824])).
% 21.78/11.57  tff(c_69402, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_68963, c_69395])).
% 21.78/11.57  tff(c_69406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_69402])).
% 21.78/11.57  tff(c_69407, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_64])).
% 21.78/11.57  tff(c_69408, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 21.78/11.57  tff(c_69417, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69407, c_69408])).
% 21.78/11.57  tff(c_69423, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_69417, c_68])).
% 21.78/11.57  tff(c_69446, plain, (![C_1817, A_1818, B_1819]: (v1_relat_1(C_1817) | ~m1_subset_1(C_1817, k1_zfmisc_1(k2_zfmisc_1(A_1818, B_1819))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 21.78/11.57  tff(c_69455, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_69423, c_69446])).
% 21.78/11.57  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 21.78/11.57  tff(c_69412, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69407, c_2])).
% 21.78/11.57  tff(c_71619, plain, (![C_2073, A_2074, B_2075]: (v1_xboole_0(C_2073) | ~m1_subset_1(C_2073, k1_zfmisc_1(k2_zfmisc_1(A_2074, B_2075))) | ~v1_xboole_0(A_2074))), inference(cnfTransformation, [status(thm)], [f_94])).
% 21.78/11.57  tff(c_71629, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_69423, c_71619])).
% 21.78/11.57  tff(c_71635, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69412, c_71629])).
% 21.78/11.57  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 21.78/11.57  tff(c_69433, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_69407, c_4])).
% 21.78/11.57  tff(c_71642, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_71635, c_69433])).
% 21.78/11.57  tff(c_10, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 21.78/11.57  tff(c_69409, plain, (![A_7]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_69407, c_10])).
% 21.78/11.57  tff(c_69454, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_69409, c_69446])).
% 21.78/11.57  tff(c_70077, plain, (![C_1902, B_1903, A_1904]: (v5_relat_1(C_1902, B_1903) | ~m1_subset_1(C_1902, k1_zfmisc_1(k2_zfmisc_1(A_1904, B_1903))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 21.78/11.57  tff(c_70085, plain, (![B_1903]: (v5_relat_1('#skF_1', B_1903))), inference(resolution, [status(thm)], [c_69409, c_70077])).
% 21.78/11.57  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 21.78/11.57  tff(c_69410, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69407, c_69407, c_20])).
% 21.78/11.57  tff(c_71441, plain, (![B_2051, A_2052]: (r1_tarski(k2_relat_1(B_2051), A_2052) | ~v5_relat_1(B_2051, A_2052) | ~v1_relat_1(B_2051))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.78/11.57  tff(c_71453, plain, (![A_2052]: (r1_tarski('#skF_1', A_2052) | ~v5_relat_1('#skF_1', A_2052) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_69410, c_71441])).
% 21.78/11.57  tff(c_71458, plain, (![A_2052]: (r1_tarski('#skF_1', A_2052))), inference(demodulation, [status(thm), theory('equality')], [c_69454, c_70085, c_71453])).
% 21.78/11.57  tff(c_71651, plain, (![A_2052]: (r1_tarski('#skF_4', A_2052))), inference(demodulation, [status(thm), theory('equality')], [c_71642, c_71458])).
% 21.78/11.57  tff(c_71668, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_71642, c_71642, c_69410])).
% 21.78/11.57  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 21.78/11.57  tff(c_69411, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69407, c_69407, c_22])).
% 21.78/11.57  tff(c_71669, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_71642, c_71642, c_69411])).
% 21.78/11.57  tff(c_71880, plain, (![B_2094, A_2095]: (v1_funct_2(B_2094, k1_relat_1(B_2094), A_2095) | ~r1_tarski(k2_relat_1(B_2094), A_2095) | ~v1_funct_1(B_2094) | ~v1_relat_1(B_2094))), inference(cnfTransformation, [status(thm)], [f_142])).
% 21.78/11.57  tff(c_71883, plain, (![A_2095]: (v1_funct_2('#skF_4', '#skF_4', A_2095) | ~r1_tarski(k2_relat_1('#skF_4'), A_2095) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_71669, c_71880])).
% 21.78/11.57  tff(c_71885, plain, (![A_2095]: (v1_funct_2('#skF_4', '#skF_4', A_2095))), inference(demodulation, [status(thm), theory('equality')], [c_69455, c_72, c_71651, c_71668, c_71883])).
% 21.78/11.57  tff(c_70049, plain, (![C_1896, A_1897, B_1898]: (v4_relat_1(C_1896, A_1897) | ~m1_subset_1(C_1896, k1_zfmisc_1(k2_zfmisc_1(A_1897, B_1898))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 21.78/11.57  tff(c_70057, plain, (![A_1897]: (v4_relat_1('#skF_1', A_1897))), inference(resolution, [status(thm)], [c_69409, c_70049])).
% 21.78/11.57  tff(c_70060, plain, (![B_1900, A_1901]: (k7_relat_1(B_1900, A_1901)=B_1900 | ~v4_relat_1(B_1900, A_1901) | ~v1_relat_1(B_1900))), inference(cnfTransformation, [status(thm)], [f_64])).
% 21.78/11.57  tff(c_70066, plain, (![A_1897]: (k7_relat_1('#skF_1', A_1897)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_70057, c_70060])).
% 21.78/11.57  tff(c_70072, plain, (![A_1897]: (k7_relat_1('#skF_1', A_1897)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69454, c_70066])).
% 21.78/11.57  tff(c_71657, plain, (![A_1897]: (k7_relat_1('#skF_4', A_1897)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_71642, c_71642, c_70072])).
% 21.78/11.57  tff(c_71460, plain, (![A_2053]: (r1_tarski('#skF_1', A_2053))), inference(demodulation, [status(thm), theory('equality')], [c_69454, c_70085, c_71453])).
% 21.78/11.57  tff(c_71470, plain, (![A_2054, A_2055]: (r1_tarski(A_2054, A_2055) | ~r1_tarski(A_2054, '#skF_1'))), inference(resolution, [status(thm)], [c_71460, c_6])).
% 21.78/11.57  tff(c_71482, plain, (![A_2055]: (r1_tarski('#skF_3', A_2055))), inference(resolution, [status(thm)], [c_66, c_71470])).
% 21.78/11.57  tff(c_71731, plain, (![B_2078, A_2079]: (k1_relat_1(k7_relat_1(B_2078, A_2079))=A_2079 | ~r1_tarski(A_2079, k1_relat_1(B_2078)) | ~v1_relat_1(B_2078))), inference(cnfTransformation, [status(thm)], [f_73])).
% 21.78/11.57  tff(c_71841, plain, (![B_2091]: (k1_relat_1(k7_relat_1(B_2091, '#skF_3'))='#skF_3' | ~v1_relat_1(B_2091))), inference(resolution, [status(thm)], [c_71482, c_71731])).
% 21.78/11.57  tff(c_71854, plain, (k1_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_71657, c_71841])).
% 21.78/11.57  tff(c_71858, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69455, c_71669, c_71854])).
% 21.78/11.57  tff(c_70329, plain, (![C_1940, A_1941, B_1942]: (v1_xboole_0(C_1940) | ~m1_subset_1(C_1940, k1_zfmisc_1(k2_zfmisc_1(A_1941, B_1942))) | ~v1_xboole_0(A_1941))), inference(cnfTransformation, [status(thm)], [f_94])).
% 21.78/11.57  tff(c_70336, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_69423, c_70329])).
% 21.78/11.57  tff(c_70341, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69412, c_70336])).
% 21.78/11.57  tff(c_70348, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_70341, c_69433])).
% 21.78/11.57  tff(c_70366, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_70348, c_69409])).
% 21.78/11.57  tff(c_70356, plain, (![A_1897]: (k7_relat_1('#skF_4', A_1897)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70348, c_70348, c_70072])).
% 21.78/11.57  tff(c_71349, plain, (![A_2039, B_2040, C_2041, D_2042]: (k2_partfun1(A_2039, B_2040, C_2041, D_2042)=k7_relat_1(C_2041, D_2042) | ~m1_subset_1(C_2041, k1_zfmisc_1(k2_zfmisc_1(A_2039, B_2040))) | ~v1_funct_1(C_2041))), inference(cnfTransformation, [status(thm)], [f_130])).
% 21.78/11.57  tff(c_71354, plain, (![A_2039, B_2040, D_2042]: (k2_partfun1(A_2039, B_2040, '#skF_4', D_2042)=k7_relat_1('#skF_4', D_2042) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_70366, c_71349])).
% 21.78/11.57  tff(c_71358, plain, (![A_2039, B_2040, D_2042]: (k2_partfun1(A_2039, B_2040, '#skF_4', D_2042)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70356, c_71354])).
% 21.78/11.57  tff(c_70368, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70348, c_70348, c_69411])).
% 21.78/11.57  tff(c_70129, plain, (![B_1911, A_1912]: (r1_tarski(k2_relat_1(B_1911), A_1912) | ~v5_relat_1(B_1911, A_1912) | ~v1_relat_1(B_1911))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.78/11.57  tff(c_70135, plain, (![A_1912]: (r1_tarski('#skF_1', A_1912) | ~v5_relat_1('#skF_1', A_1912) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_69410, c_70129])).
% 21.78/11.57  tff(c_70138, plain, (![A_1912]: (r1_tarski('#skF_1', A_1912))), inference(demodulation, [status(thm), theory('equality')], [c_69454, c_70085, c_70135])).
% 21.78/11.57  tff(c_70141, plain, (![A_1914, C_1915, B_1916]: (r1_tarski(A_1914, C_1915) | ~r1_tarski(B_1916, C_1915) | ~r1_tarski(A_1914, B_1916))), inference(cnfTransformation, [status(thm)], [f_36])).
% 21.78/11.57  tff(c_70169, plain, (![A_1918, A_1919]: (r1_tarski(A_1918, A_1919) | ~r1_tarski(A_1918, '#skF_1'))), inference(resolution, [status(thm)], [c_70138, c_70141])).
% 21.78/11.57  tff(c_70181, plain, (![A_1919]: (r1_tarski('#skF_3', A_1919))), inference(resolution, [status(thm)], [c_66, c_70169])).
% 21.78/11.57  tff(c_70435, plain, (![B_1945, A_1946]: (k1_relat_1(k7_relat_1(B_1945, A_1946))=A_1946 | ~r1_tarski(A_1946, k1_relat_1(B_1945)) | ~v1_relat_1(B_1945))), inference(cnfTransformation, [status(thm)], [f_73])).
% 21.78/11.57  tff(c_70544, plain, (![B_1958]: (k1_relat_1(k7_relat_1(B_1958, '#skF_3'))='#skF_3' | ~v1_relat_1(B_1958))), inference(resolution, [status(thm)], [c_70181, c_70435])).
% 21.78/11.57  tff(c_70557, plain, (k1_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_70356, c_70544])).
% 21.78/11.57  tff(c_70561, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69455, c_70368, c_70557])).
% 21.78/11.57  tff(c_69716, plain, (![C_1862, A_1863, B_1864]: (v1_xboole_0(C_1862) | ~m1_subset_1(C_1862, k1_zfmisc_1(k2_zfmisc_1(A_1863, B_1864))) | ~v1_xboole_0(A_1863))), inference(cnfTransformation, [status(thm)], [f_94])).
% 21.78/11.57  tff(c_69723, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_69423, c_69716])).
% 21.78/11.57  tff(c_69728, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69412, c_69723])).
% 21.78/11.57  tff(c_69735, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_69728, c_69433])).
% 21.78/11.57  tff(c_69751, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_69735, c_69409])).
% 21.78/11.57  tff(c_70037, plain, (![A_1892, B_1893, C_1894, D_1895]: (v1_funct_1(k2_partfun1(A_1892, B_1893, C_1894, D_1895)) | ~m1_subset_1(C_1894, k1_zfmisc_1(k2_zfmisc_1(A_1892, B_1893))) | ~v1_funct_1(C_1894))), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.78/11.57  tff(c_70040, plain, (![A_1892, B_1893, D_1895]: (v1_funct_1(k2_partfun1(A_1892, B_1893, '#skF_4', D_1895)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_69751, c_70037])).
% 21.78/11.57  tff(c_70043, plain, (![A_1892, B_1893, D_1895]: (v1_funct_1(k2_partfun1(A_1892, B_1893, '#skF_4', D_1895)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70040])).
% 21.78/11.57  tff(c_69753, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69735, c_69735, c_69411])).
% 21.78/11.57  tff(c_69555, plain, (![C_1837, A_1838, B_1839]: (v4_relat_1(C_1837, A_1838) | ~m1_subset_1(C_1837, k1_zfmisc_1(k2_zfmisc_1(A_1838, B_1839))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 21.78/11.57  tff(c_69563, plain, (![A_1838]: (v4_relat_1('#skF_1', A_1838))), inference(resolution, [status(thm)], [c_69409, c_69555])).
% 21.78/11.57  tff(c_69631, plain, (![B_1849, A_1850]: (k7_relat_1(B_1849, A_1850)=B_1849 | ~v4_relat_1(B_1849, A_1850) | ~v1_relat_1(B_1849))), inference(cnfTransformation, [status(thm)], [f_64])).
% 21.78/11.57  tff(c_69637, plain, (![A_1838]: (k7_relat_1('#skF_1', A_1838)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_69563, c_69631])).
% 21.78/11.57  tff(c_69643, plain, (![A_1838]: (k7_relat_1('#skF_1', A_1838)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69454, c_69637])).
% 21.78/11.57  tff(c_69738, plain, (![A_1838]: (k7_relat_1('#skF_4', A_1838)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69735, c_69735, c_69643])).
% 21.78/11.57  tff(c_69458, plain, (![C_1820, B_1821, A_1822]: (v5_relat_1(C_1820, B_1821) | ~m1_subset_1(C_1820, k1_zfmisc_1(k2_zfmisc_1(A_1822, B_1821))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 21.78/11.57  tff(c_69466, plain, (![B_1821]: (v5_relat_1('#skF_1', B_1821))), inference(resolution, [status(thm)], [c_69409, c_69458])).
% 21.78/11.57  tff(c_69474, plain, (![B_1828, A_1829]: (r1_tarski(k2_relat_1(B_1828), A_1829) | ~v5_relat_1(B_1828, A_1829) | ~v1_relat_1(B_1828))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.78/11.57  tff(c_69483, plain, (![A_1829]: (r1_tarski('#skF_1', A_1829) | ~v5_relat_1('#skF_1', A_1829) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_69410, c_69474])).
% 21.78/11.57  tff(c_69497, plain, (![A_1831]: (r1_tarski('#skF_1', A_1831))), inference(demodulation, [status(thm), theory('equality')], [c_69454, c_69466, c_69483])).
% 21.78/11.57  tff(c_69508, plain, (![A_1832, A_1833]: (r1_tarski(A_1832, A_1833) | ~r1_tarski(A_1832, '#skF_1'))), inference(resolution, [status(thm)], [c_69497, c_6])).
% 21.78/11.57  tff(c_69523, plain, (![A_1833]: (r1_tarski('#skF_3', A_1833))), inference(resolution, [status(thm)], [c_66, c_69508])).
% 21.78/11.57  tff(c_69798, plain, (![B_1868, A_1869]: (k1_relat_1(k7_relat_1(B_1868, A_1869))=A_1869 | ~r1_tarski(A_1869, k1_relat_1(B_1868)) | ~v1_relat_1(B_1868))), inference(cnfTransformation, [status(thm)], [f_73])).
% 21.78/11.57  tff(c_69977, plain, (![B_1887]: (k1_relat_1(k7_relat_1(B_1887, '#skF_3'))='#skF_3' | ~v1_relat_1(B_1887))), inference(resolution, [status(thm)], [c_69523, c_69798])).
% 21.78/11.57  tff(c_69993, plain, (k1_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_69738, c_69977])).
% 21.78/11.57  tff(c_69997, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69455, c_69753, c_69993])).
% 21.78/11.57  tff(c_69456, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_69417, c_69417, c_69417, c_69417, c_69417, c_62])).
% 21.78/11.57  tff(c_69457, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_69456])).
% 21.78/11.57  tff(c_69746, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_69735, c_69735, c_69457])).
% 21.78/11.57  tff(c_69999, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_69997, c_69746])).
% 21.78/11.57  tff(c_70046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70043, c_69999])).
% 21.78/11.57  tff(c_70047, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitRight, [status(thm)], [c_69456])).
% 21.78/11.57  tff(c_70095, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitLeft, [status(thm)], [c_70047])).
% 21.78/11.57  tff(c_70349, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_70348, c_70348, c_70348, c_70095])).
% 21.78/11.57  tff(c_70694, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_70561, c_70561, c_70349])).
% 21.78/11.57  tff(c_71360, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_71358, c_70694])).
% 21.78/11.57  tff(c_71364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70366, c_71360])).
% 21.78/11.57  tff(c_71366, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitRight, [status(thm)], [c_70047])).
% 21.78/11.57  tff(c_71630, plain, (v1_xboole_0(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_71366, c_71619])).
% 21.78/11.57  tff(c_71919, plain, (v1_xboole_0(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_71635, c_71858, c_71858, c_71642, c_71642, c_71630])).
% 21.78/11.57  tff(c_8, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 21.78/11.57  tff(c_71641, plain, (![A_5]: (A_5='#skF_4' | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_71635, c_8])).
% 21.78/11.57  tff(c_71925, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_71919, c_71641])).
% 21.78/11.57  tff(c_71365, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_70047])).
% 21.78/11.57  tff(c_71656, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_71642, c_71642, c_71642, c_71365])).
% 21.78/11.57  tff(c_71950, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71885, c_71925, c_71858, c_71858, c_71656])).
% 21.78/11.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.78/11.57  
% 21.78/11.57  Inference rules
% 21.78/11.57  ----------------------
% 21.78/11.57  #Ref     : 0
% 21.78/11.57  #Sup     : 15485
% 21.78/11.57  #Fact    : 0
% 21.78/11.57  #Define  : 0
% 21.78/11.57  #Split   : 44
% 21.78/11.57  #Chain   : 0
% 21.78/11.57  #Close   : 0
% 21.78/11.57  
% 21.78/11.57  Ordering : KBO
% 21.78/11.57  
% 21.78/11.57  Simplification rules
% 21.78/11.57  ----------------------
% 21.78/11.57  #Subsume      : 5459
% 21.78/11.57  #Demod        : 27341
% 21.78/11.57  #Tautology    : 5486
% 21.78/11.57  #SimpNegUnit  : 225
% 21.78/11.57  #BackRed      : 185
% 21.78/11.57  
% 21.78/11.57  #Partial instantiations: 0
% 21.78/11.57  #Strategies tried      : 1
% 21.78/11.57  
% 21.78/11.57  Timing (in seconds)
% 21.78/11.57  ----------------------
% 21.78/11.57  Preprocessing        : 0.34
% 21.78/11.57  Parsing              : 0.18
% 21.78/11.57  CNF conversion       : 0.02
% 21.78/11.57  Main loop            : 10.43
% 21.78/11.57  Inferencing          : 1.97
% 21.78/11.58  Reduction            : 4.64
% 21.78/11.58  Demodulation         : 3.80
% 21.78/11.58  BG Simplification    : 0.16
% 21.78/11.58  Subsumption          : 3.11
% 21.78/11.58  Abstraction          : 0.31
% 21.78/11.58  MUC search           : 0.00
% 21.78/11.58  Cooper               : 0.00
% 21.78/11.58  Total                : 10.85
% 21.78/11.58  Index Insertion      : 0.00
% 21.78/11.58  Index Deletion       : 0.00
% 21.78/11.58  Index Matching       : 0.00
% 21.78/11.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
