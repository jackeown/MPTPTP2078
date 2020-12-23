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
% DateTime   : Thu Dec  3 10:12:05 EST 2020

% Result     : Theorem 5.33s
% Output     : CNFRefutation 5.60s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 539 expanded)
%              Number of leaves         :   42 ( 203 expanded)
%              Depth                    :   10
%              Number of atoms          :  236 (1562 expanded)
%              Number of equality atoms :   56 ( 194 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_157,negated_conjecture,(
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

tff(f_98,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_96,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_76,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_137,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_48,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_115,axiom,(
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

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_50,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_122,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_42,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_18,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_66,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_18])).

tff(c_38,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] :
      ( m1_subset_1(k1_partfun1(A_25,B_26,C_27,D_28,E_29,F_30),k1_zfmisc_1(k2_zfmisc_1(A_25,D_28)))
      | ~ m1_subset_1(F_30,k1_zfmisc_1(k2_zfmisc_1(C_27,D_28)))
      | ~ v1_funct_1(F_30)
      | ~ m1_subset_1(E_29,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(E_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    ! [A_22] : m1_subset_1(k6_relat_1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_65,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_32])).

tff(c_52,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_811,plain,(
    ! [D_161,C_162,A_163,B_164] :
      ( D_161 = C_162
      | ~ r2_relset_1(A_163,B_164,C_162,D_161)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164)))
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_821,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_52,c_811])).

tff(c_840,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_821])).

tff(c_1271,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_840])).

tff(c_1274,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_1271])).

tff(c_1278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_58,c_54,c_1274])).

tff(c_1279,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_840])).

tff(c_1300,plain,(
    ! [E_256,D_255,B_254,C_257,A_253] :
      ( k1_xboole_0 = C_257
      | v2_funct_1(D_255)
      | ~ v2_funct_1(k1_partfun1(A_253,B_254,B_254,C_257,D_255,E_256))
      | ~ m1_subset_1(E_256,k1_zfmisc_1(k2_zfmisc_1(B_254,C_257)))
      | ~ v1_funct_2(E_256,B_254,C_257)
      | ~ v1_funct_1(E_256)
      | ~ m1_subset_1(D_255,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254)))
      | ~ v1_funct_2(D_255,A_253,B_254)
      | ~ v1_funct_1(D_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1302,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1279,c_1300])).

tff(c_1304,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_56,c_54,c_66,c_1302])).

tff(c_1305,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_1304])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1340,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_2])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1338,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_1305,c_8])).

tff(c_149,plain,(
    ! [B_53,A_54] :
      ( v1_xboole_0(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_166,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_149])).

tff(c_169,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_1475,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1338,c_169])).

tff(c_1479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1340,c_1475])).

tff(c_1480,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_123,plain,(
    ! [B_49,A_50] :
      ( ~ v1_xboole_0(B_49)
      | B_49 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_126,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_2,c_123])).

tff(c_1498,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1480,c_126])).

tff(c_98,plain,(
    ! [A_48] : k6_relat_1(A_48) = k6_partfun1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_104,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_14])).

tff(c_117,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_66])).

tff(c_1503,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1498,c_117])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1506,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1498,c_1498,c_10])).

tff(c_1507,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1498,c_1498,c_8])).

tff(c_1481,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1595,plain,(
    ! [A_281] :
      ( A_281 = '#skF_4'
      | ~ v1_xboole_0(A_281) ) ),
    inference(resolution,[status(thm)],[c_1480,c_4])).

tff(c_1602,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1481,c_1595])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1720,plain,(
    ! [B_301,A_302] :
      ( B_301 = '#skF_4'
      | A_302 = '#skF_4'
      | k2_zfmisc_1(A_302,B_301) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1498,c_1498,c_1498,c_6])).

tff(c_1730,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1602,c_1720])).

tff(c_1735,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1730])).

tff(c_167,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_149])).

tff(c_1515,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_1738,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1735,c_1515])).

tff(c_1746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1480,c_1507,c_1738])).

tff(c_1747,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1730])).

tff(c_1751,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1747,c_1515])).

tff(c_1759,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1480,c_1506,c_1751])).

tff(c_1760,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_1828,plain,(
    ! [A_310] :
      ( A_310 = '#skF_4'
      | ~ v1_xboole_0(A_310) ) ),
    inference(resolution,[status(thm)],[c_1480,c_4])).

tff(c_1843,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1760,c_1828])).

tff(c_1851,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1843,c_122])).

tff(c_1858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1503,c_1851])).

tff(c_1859,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1919,plain,(
    ! [C_319,A_320,B_321] :
      ( v1_relat_1(C_319)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_320,B_321))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1935,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1919])).

tff(c_1957,plain,(
    ! [C_324,B_325,A_326] :
      ( v5_relat_1(C_324,B_325)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(k2_zfmisc_1(A_326,B_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1974,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_1957])).

tff(c_2065,plain,(
    ! [A_343,B_344,D_345] :
      ( r2_relset_1(A_343,B_344,D_345,D_345)
      | ~ m1_subset_1(D_345,k1_zfmisc_1(k2_zfmisc_1(A_343,B_344))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2076,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_65,c_2065])).

tff(c_2081,plain,(
    ! [A_347,B_348,C_349] :
      ( k2_relset_1(A_347,B_348,C_349) = k2_relat_1(C_349)
      | ~ m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(A_347,B_348))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2098,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_2081])).

tff(c_2272,plain,(
    ! [C_381,A_380,B_383,D_379,F_382,E_384] :
      ( m1_subset_1(k1_partfun1(A_380,B_383,C_381,D_379,E_384,F_382),k1_zfmisc_1(k2_zfmisc_1(A_380,D_379)))
      | ~ m1_subset_1(F_382,k1_zfmisc_1(k2_zfmisc_1(C_381,D_379)))
      | ~ v1_funct_1(F_382)
      | ~ m1_subset_1(E_384,k1_zfmisc_1(k2_zfmisc_1(A_380,B_383)))
      | ~ v1_funct_1(E_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2118,plain,(
    ! [D_351,C_352,A_353,B_354] :
      ( D_351 = C_352
      | ~ r2_relset_1(A_353,B_354,C_352,D_351)
      | ~ m1_subset_1(D_351,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354)))
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2128,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_52,c_2118])).

tff(c_2147,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_2128])).

tff(c_2170,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2147])).

tff(c_2275,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2272,c_2170])).

tff(c_2307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_58,c_54,c_2275])).

tff(c_2308,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2147])).

tff(c_2707,plain,(
    ! [A_508,B_509,C_510,D_511] :
      ( k2_relset_1(A_508,B_509,C_510) = B_509
      | ~ r2_relset_1(B_509,B_509,k1_partfun1(B_509,A_508,A_508,B_509,D_511,C_510),k6_partfun1(B_509))
      | ~ m1_subset_1(D_511,k1_zfmisc_1(k2_zfmisc_1(B_509,A_508)))
      | ~ v1_funct_2(D_511,B_509,A_508)
      | ~ v1_funct_1(D_511)
      | ~ m1_subset_1(C_510,k1_zfmisc_1(k2_zfmisc_1(A_508,B_509)))
      | ~ v1_funct_2(C_510,A_508,B_509)
      | ~ v1_funct_1(C_510) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2710,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2308,c_2707])).

tff(c_2715,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_64,c_62,c_60,c_2076,c_2098,c_2710])).

tff(c_34,plain,(
    ! [B_24] :
      ( v2_funct_2(B_24,k2_relat_1(B_24))
      | ~ v5_relat_1(B_24,k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2721,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2715,c_34])).

tff(c_2725,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1935,c_1974,c_2715,c_2721])).

tff(c_2727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1859,c_2725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:04:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.33/2.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.01  
% 5.33/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.02  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.33/2.02  
% 5.33/2.02  %Foreground sorts:
% 5.33/2.02  
% 5.33/2.02  
% 5.33/2.02  %Background operators:
% 5.33/2.02  
% 5.33/2.02  
% 5.33/2.02  %Foreground operators:
% 5.33/2.02  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.33/2.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.33/2.02  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.33/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.33/2.02  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.33/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.33/2.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.33/2.02  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.33/2.02  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.33/2.02  tff('#skF_2', type, '#skF_2': $i).
% 5.33/2.02  tff('#skF_3', type, '#skF_3': $i).
% 5.33/2.02  tff('#skF_1', type, '#skF_1': $i).
% 5.33/2.02  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.33/2.02  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.33/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.33/2.02  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.33/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.33/2.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.33/2.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.33/2.02  tff('#skF_4', type, '#skF_4': $i).
% 5.33/2.02  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.33/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.33/2.02  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.33/2.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.33/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.33/2.02  
% 5.60/2.04  tff(f_157, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 5.60/2.04  tff(f_98, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.60/2.04  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.60/2.04  tff(f_96, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.60/2.04  tff(f_76, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.60/2.04  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.60/2.04  tff(f_137, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 5.60/2.04  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.60/2.04  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.60/2.04  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.60/2.04  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 5.60/2.04  tff(f_48, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 5.60/2.04  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.60/2.04  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.60/2.04  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.60/2.04  tff(f_115, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 5.60/2.04  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.60/2.04  tff(c_50, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.60/2.04  tff(c_122, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 5.60/2.04  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.60/2.04  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.60/2.04  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.60/2.04  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.60/2.04  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.60/2.04  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.60/2.04  tff(c_42, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.60/2.04  tff(c_18, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.60/2.04  tff(c_66, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_18])).
% 5.60/2.04  tff(c_38, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (m1_subset_1(k1_partfun1(A_25, B_26, C_27, D_28, E_29, F_30), k1_zfmisc_1(k2_zfmisc_1(A_25, D_28))) | ~m1_subset_1(F_30, k1_zfmisc_1(k2_zfmisc_1(C_27, D_28))) | ~v1_funct_1(F_30) | ~m1_subset_1(E_29, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(E_29))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.60/2.04  tff(c_32, plain, (![A_22]: (m1_subset_1(k6_relat_1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.60/2.04  tff(c_65, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_32])).
% 5.60/2.04  tff(c_52, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.60/2.04  tff(c_811, plain, (![D_161, C_162, A_163, B_164]: (D_161=C_162 | ~r2_relset_1(A_163, B_164, C_162, D_161) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.60/2.04  tff(c_821, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_52, c_811])).
% 5.60/2.04  tff(c_840, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_821])).
% 5.60/2.04  tff(c_1271, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_840])).
% 5.60/2.04  tff(c_1274, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_1271])).
% 5.60/2.04  tff(c_1278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_58, c_54, c_1274])).
% 5.60/2.04  tff(c_1279, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_840])).
% 5.60/2.04  tff(c_1300, plain, (![E_256, D_255, B_254, C_257, A_253]: (k1_xboole_0=C_257 | v2_funct_1(D_255) | ~v2_funct_1(k1_partfun1(A_253, B_254, B_254, C_257, D_255, E_256)) | ~m1_subset_1(E_256, k1_zfmisc_1(k2_zfmisc_1(B_254, C_257))) | ~v1_funct_2(E_256, B_254, C_257) | ~v1_funct_1(E_256) | ~m1_subset_1(D_255, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))) | ~v1_funct_2(D_255, A_253, B_254) | ~v1_funct_1(D_255))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.60/2.04  tff(c_1302, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1279, c_1300])).
% 5.60/2.04  tff(c_1304, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_54, c_66, c_1302])).
% 5.60/2.04  tff(c_1305, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_122, c_1304])).
% 5.60/2.04  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.60/2.04  tff(c_1340, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_2])).
% 5.60/2.04  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.60/2.04  tff(c_1338, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_1305, c_8])).
% 5.60/2.04  tff(c_149, plain, (![B_53, A_54]: (v1_xboole_0(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.60/2.04  tff(c_166, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_54, c_149])).
% 5.60/2.04  tff(c_169, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_166])).
% 5.60/2.04  tff(c_1475, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1338, c_169])).
% 5.60/2.04  tff(c_1479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1340, c_1475])).
% 5.60/2.04  tff(c_1480, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_166])).
% 5.60/2.04  tff(c_123, plain, (![B_49, A_50]: (~v1_xboole_0(B_49) | B_49=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.60/2.04  tff(c_126, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_2, c_123])).
% 5.60/2.04  tff(c_1498, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1480, c_126])).
% 5.60/2.04  tff(c_98, plain, (![A_48]: (k6_relat_1(A_48)=k6_partfun1(A_48))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.60/2.04  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.60/2.04  tff(c_104, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_98, c_14])).
% 5.60/2.04  tff(c_117, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_104, c_66])).
% 5.60/2.04  tff(c_1503, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1498, c_117])).
% 5.60/2.04  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.60/2.04  tff(c_1506, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1498, c_1498, c_10])).
% 5.60/2.04  tff(c_1507, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1498, c_1498, c_8])).
% 5.60/2.04  tff(c_1481, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_166])).
% 5.60/2.04  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.60/2.04  tff(c_1595, plain, (![A_281]: (A_281='#skF_4' | ~v1_xboole_0(A_281))), inference(resolution, [status(thm)], [c_1480, c_4])).
% 5.60/2.04  tff(c_1602, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_1481, c_1595])).
% 5.60/2.04  tff(c_6, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.60/2.04  tff(c_1720, plain, (![B_301, A_302]: (B_301='#skF_4' | A_302='#skF_4' | k2_zfmisc_1(A_302, B_301)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1498, c_1498, c_1498, c_6])).
% 5.60/2.04  tff(c_1730, plain, ('#skF_1'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1602, c_1720])).
% 5.60/2.04  tff(c_1735, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_1730])).
% 5.60/2.04  tff(c_167, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_149])).
% 5.60/2.04  tff(c_1515, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_167])).
% 5.60/2.04  tff(c_1738, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1735, c_1515])).
% 5.60/2.04  tff(c_1746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1480, c_1507, c_1738])).
% 5.60/2.04  tff(c_1747, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_1730])).
% 5.60/2.04  tff(c_1751, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1747, c_1515])).
% 5.60/2.04  tff(c_1759, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1480, c_1506, c_1751])).
% 5.60/2.04  tff(c_1760, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_167])).
% 5.60/2.04  tff(c_1828, plain, (![A_310]: (A_310='#skF_4' | ~v1_xboole_0(A_310))), inference(resolution, [status(thm)], [c_1480, c_4])).
% 5.60/2.04  tff(c_1843, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1760, c_1828])).
% 5.60/2.04  tff(c_1851, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1843, c_122])).
% 5.60/2.04  tff(c_1858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1503, c_1851])).
% 5.60/2.04  tff(c_1859, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 5.60/2.04  tff(c_1919, plain, (![C_319, A_320, B_321]: (v1_relat_1(C_319) | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(A_320, B_321))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.60/2.04  tff(c_1935, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_1919])).
% 5.60/2.04  tff(c_1957, plain, (![C_324, B_325, A_326]: (v5_relat_1(C_324, B_325) | ~m1_subset_1(C_324, k1_zfmisc_1(k2_zfmisc_1(A_326, B_325))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.60/2.04  tff(c_1974, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_1957])).
% 5.60/2.04  tff(c_2065, plain, (![A_343, B_344, D_345]: (r2_relset_1(A_343, B_344, D_345, D_345) | ~m1_subset_1(D_345, k1_zfmisc_1(k2_zfmisc_1(A_343, B_344))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.60/2.04  tff(c_2076, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_65, c_2065])).
% 5.60/2.04  tff(c_2081, plain, (![A_347, B_348, C_349]: (k2_relset_1(A_347, B_348, C_349)=k2_relat_1(C_349) | ~m1_subset_1(C_349, k1_zfmisc_1(k2_zfmisc_1(A_347, B_348))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.60/2.04  tff(c_2098, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_2081])).
% 5.60/2.04  tff(c_2272, plain, (![C_381, A_380, B_383, D_379, F_382, E_384]: (m1_subset_1(k1_partfun1(A_380, B_383, C_381, D_379, E_384, F_382), k1_zfmisc_1(k2_zfmisc_1(A_380, D_379))) | ~m1_subset_1(F_382, k1_zfmisc_1(k2_zfmisc_1(C_381, D_379))) | ~v1_funct_1(F_382) | ~m1_subset_1(E_384, k1_zfmisc_1(k2_zfmisc_1(A_380, B_383))) | ~v1_funct_1(E_384))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.60/2.04  tff(c_2118, plain, (![D_351, C_352, A_353, B_354]: (D_351=C_352 | ~r2_relset_1(A_353, B_354, C_352, D_351) | ~m1_subset_1(D_351, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))) | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.60/2.04  tff(c_2128, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_52, c_2118])).
% 5.60/2.04  tff(c_2147, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_2128])).
% 5.60/2.04  tff(c_2170, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2147])).
% 5.60/2.04  tff(c_2275, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2272, c_2170])).
% 5.60/2.04  tff(c_2307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_58, c_54, c_2275])).
% 5.60/2.04  tff(c_2308, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2147])).
% 5.60/2.04  tff(c_2707, plain, (![A_508, B_509, C_510, D_511]: (k2_relset_1(A_508, B_509, C_510)=B_509 | ~r2_relset_1(B_509, B_509, k1_partfun1(B_509, A_508, A_508, B_509, D_511, C_510), k6_partfun1(B_509)) | ~m1_subset_1(D_511, k1_zfmisc_1(k2_zfmisc_1(B_509, A_508))) | ~v1_funct_2(D_511, B_509, A_508) | ~v1_funct_1(D_511) | ~m1_subset_1(C_510, k1_zfmisc_1(k2_zfmisc_1(A_508, B_509))) | ~v1_funct_2(C_510, A_508, B_509) | ~v1_funct_1(C_510))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.60/2.04  tff(c_2710, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2308, c_2707])).
% 5.60/2.04  tff(c_2715, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_64, c_62, c_60, c_2076, c_2098, c_2710])).
% 5.60/2.04  tff(c_34, plain, (![B_24]: (v2_funct_2(B_24, k2_relat_1(B_24)) | ~v5_relat_1(B_24, k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.60/2.04  tff(c_2721, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2715, c_34])).
% 5.60/2.04  tff(c_2725, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1935, c_1974, c_2715, c_2721])).
% 5.60/2.04  tff(c_2727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1859, c_2725])).
% 5.60/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.60/2.04  
% 5.60/2.04  Inference rules
% 5.60/2.04  ----------------------
% 5.60/2.04  #Ref     : 0
% 5.60/2.04  #Sup     : 590
% 5.60/2.04  #Fact    : 0
% 5.60/2.04  #Define  : 0
% 5.60/2.04  #Split   : 18
% 5.60/2.04  #Chain   : 0
% 5.60/2.04  #Close   : 0
% 5.60/2.04  
% 5.60/2.04  Ordering : KBO
% 5.60/2.04  
% 5.60/2.04  Simplification rules
% 5.60/2.04  ----------------------
% 5.60/2.04  #Subsume      : 48
% 5.60/2.04  #Demod        : 616
% 5.60/2.04  #Tautology    : 226
% 5.60/2.04  #SimpNegUnit  : 6
% 5.60/2.04  #BackRed      : 148
% 5.60/2.04  
% 5.60/2.04  #Partial instantiations: 0
% 5.60/2.04  #Strategies tried      : 1
% 5.60/2.04  
% 5.60/2.04  Timing (in seconds)
% 5.60/2.04  ----------------------
% 5.60/2.05  Preprocessing        : 0.35
% 5.60/2.05  Parsing              : 0.19
% 5.60/2.05  CNF conversion       : 0.02
% 5.60/2.05  Main loop            : 0.90
% 5.60/2.05  Inferencing          : 0.30
% 5.60/2.05  Reduction            : 0.32
% 5.60/2.05  Demodulation         : 0.23
% 5.60/2.05  BG Simplification    : 0.03
% 5.60/2.05  Subsumption          : 0.16
% 5.60/2.05  Abstraction          : 0.04
% 5.60/2.05  MUC search           : 0.00
% 5.60/2.05  Cooper               : 0.00
% 5.60/2.05  Total                : 1.30
% 5.60/2.05  Index Insertion      : 0.00
% 5.60/2.05  Index Deletion       : 0.00
% 5.60/2.05  Index Matching       : 0.00
% 5.60/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
