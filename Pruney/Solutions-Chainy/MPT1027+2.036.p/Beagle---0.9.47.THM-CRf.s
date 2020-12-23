%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:47 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 477 expanded)
%              Number of leaves         :   32 ( 175 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 (1080 expanded)
%              Number of equality atoms :   42 ( 304 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_77,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
      & v1_relat_1(B)
      & v4_relat_1(B,A)
      & v5_relat_1(B,A)
      & v1_funct_1(B)
      & v1_funct_2(B,A,A)
      & v3_funct_2(B,A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_funct_2)).

tff(c_6,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_54,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46])).

tff(c_48,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_420,plain,(
    ! [B_60,C_61,A_62] :
      ( k1_xboole_0 = B_60
      | v1_funct_2(C_61,A_62,B_60)
      | k1_relset_1(A_62,B_60,C_61) != A_62
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_426,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_50,c_420])).

tff(c_437,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_426])).

tff(c_438,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_437])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_465,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_2])).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_462,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_438,c_10])).

tff(c_168,plain,(
    ! [C_34,B_35,A_36] :
      ( ~ v1_xboole_0(C_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(C_34))
      | ~ r2_hidden(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_179,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_36,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_168])).

tff(c_290,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_534,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_290])).

tff(c_538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_534])).

tff(c_542,plain,(
    ! [A_70] : ~ r2_hidden(A_70,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_547,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6,c_542])).

tff(c_97,plain,(
    ! [A_27] :
      ( v1_xboole_0(k1_relat_1(A_27))
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_102,plain,(
    ! [A_28] :
      ( k1_relat_1(A_28) = k1_xboole_0
      | ~ v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_97,c_4])).

tff(c_110,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_102])).

tff(c_558,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_547,c_110])).

tff(c_604,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_610,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_604])).

tff(c_613,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_48,c_610])).

tff(c_623,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_48])).

tff(c_20,plain,(
    ! [A_13] :
      ( v1_funct_2(k1_xboole_0,A_13,k1_xboole_0)
      | k1_xboole_0 = A_13
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_13,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_58,plain,(
    ! [A_13] :
      ( v1_funct_2(k1_xboole_0,A_13,k1_xboole_0)
      | k1_xboole_0 = A_13
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20])).

tff(c_186,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_147,plain,(
    ! [A_31] : m1_subset_1('#skF_2'(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_151,plain,(
    m1_subset_1('#skF_2'(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_147])).

tff(c_170,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_36,'#skF_2'(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_151,c_168])).

tff(c_180,plain,(
    ! [A_37] : ~ r2_hidden(A_37,'#skF_2'(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_170])).

tff(c_185,plain,(
    '#skF_2'(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_180])).

tff(c_188,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_151])).

tff(c_248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_188])).

tff(c_250,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_551,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_547,c_250])).

tff(c_710,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_613,c_551])).

tff(c_620,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_547])).

tff(c_12,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [C_15,B_14] :
      ( v1_funct_2(C_15,k1_xboole_0,B_14)
      | k1_relset_1(k1_xboole_0,B_14,C_15) != k1_xboole_0
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_56,plain,(
    ! [C_15,B_14] :
      ( v1_funct_2(C_15,k1_xboole_0,B_14)
      | k1_relset_1(k1_xboole_0,B_14,C_15) != k1_xboole_0
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_24])).

tff(c_786,plain,(
    ! [C_82,B_83] :
      ( v1_funct_2(C_82,'#skF_3',B_83)
      | k1_relset_1('#skF_3',B_83,C_82) != '#skF_3'
      | ~ m1_subset_1(C_82,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_620,c_620,c_620,c_56])).

tff(c_954,plain,(
    ! [B_101] :
      ( v1_funct_2('#skF_3','#skF_3',B_101)
      | k1_relset_1('#skF_3',B_101,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_710,c_786])).

tff(c_624,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_54])).

tff(c_957,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_954,c_624])).

tff(c_966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_957])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:20:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.38  
% 2.88/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.38  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.88/1.38  
% 2.88/1.38  %Foreground sorts:
% 2.88/1.38  
% 2.88/1.38  
% 2.88/1.38  %Background operators:
% 2.88/1.38  
% 2.88/1.38  
% 2.88/1.38  %Foreground operators:
% 2.88/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.88/1.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.88/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.88/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.88/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.88/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.88/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.88/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.88/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.88/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.88/1.38  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 2.88/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.88/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.88/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.38  
% 2.88/1.40  tff(f_38, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.88/1.40  tff(f_105, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 2.88/1.40  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.88/1.40  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.88/1.40  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.88/1.40  tff(f_51, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.88/1.40  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.88/1.40  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.88/1.40  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.88/1.40  tff(f_92, axiom, (![A]: (?[B]: ((((((m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) & v1_relat_1(B)) & v4_relat_1(B, A)) & v5_relat_1(B, A)) & v1_funct_1(B)) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_funct_2)).
% 2.88/1.40  tff(c_6, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.88/1.40  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.88/1.40  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.88/1.40  tff(c_46, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.88/1.40  tff(c_54, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46])).
% 2.88/1.40  tff(c_48, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.88/1.40  tff(c_420, plain, (![B_60, C_61, A_62]: (k1_xboole_0=B_60 | v1_funct_2(C_61, A_62, B_60) | k1_relset_1(A_62, B_60, C_61)!=A_62 | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_60))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.88/1.40  tff(c_426, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_50, c_420])).
% 2.88/1.40  tff(c_437, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_426])).
% 2.88/1.40  tff(c_438, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_437])).
% 2.88/1.40  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.88/1.40  tff(c_465, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_438, c_2])).
% 2.88/1.40  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.88/1.40  tff(c_462, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_438, c_438, c_10])).
% 2.88/1.40  tff(c_168, plain, (![C_34, B_35, A_36]: (~v1_xboole_0(C_34) | ~m1_subset_1(B_35, k1_zfmisc_1(C_34)) | ~r2_hidden(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.88/1.40  tff(c_179, plain, (![A_36]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_36, '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_168])).
% 2.88/1.40  tff(c_290, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_179])).
% 2.88/1.40  tff(c_534, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_462, c_290])).
% 2.88/1.40  tff(c_538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_465, c_534])).
% 2.88/1.40  tff(c_542, plain, (![A_70]: (~r2_hidden(A_70, '#skF_5'))), inference(splitRight, [status(thm)], [c_179])).
% 2.88/1.40  tff(c_547, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_6, c_542])).
% 2.88/1.40  tff(c_97, plain, (![A_27]: (v1_xboole_0(k1_relat_1(A_27)) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.88/1.40  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.88/1.40  tff(c_102, plain, (![A_28]: (k1_relat_1(A_28)=k1_xboole_0 | ~v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_97, c_4])).
% 2.88/1.40  tff(c_110, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_102])).
% 2.88/1.40  tff(c_558, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_547, c_547, c_110])).
% 2.88/1.40  tff(c_604, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.88/1.40  tff(c_610, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_604])).
% 2.88/1.40  tff(c_613, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_558, c_48, c_610])).
% 2.88/1.40  tff(c_623, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_613, c_48])).
% 2.88/1.40  tff(c_20, plain, (![A_13]: (v1_funct_2(k1_xboole_0, A_13, k1_xboole_0) | k1_xboole_0=A_13 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_13, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.88/1.40  tff(c_58, plain, (![A_13]: (v1_funct_2(k1_xboole_0, A_13, k1_xboole_0) | k1_xboole_0=A_13 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20])).
% 2.88/1.40  tff(c_186, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_58])).
% 2.88/1.40  tff(c_147, plain, (![A_31]: (m1_subset_1('#skF_2'(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.88/1.40  tff(c_151, plain, (m1_subset_1('#skF_2'(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_147])).
% 2.88/1.40  tff(c_170, plain, (![A_36]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_36, '#skF_2'(k1_xboole_0)))), inference(resolution, [status(thm)], [c_151, c_168])).
% 2.88/1.40  tff(c_180, plain, (![A_37]: (~r2_hidden(A_37, '#skF_2'(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_170])).
% 2.88/1.40  tff(c_185, plain, ('#skF_2'(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_180])).
% 2.88/1.40  tff(c_188, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_151])).
% 2.88/1.40  tff(c_248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_188])).
% 2.88/1.40  tff(c_250, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_58])).
% 2.88/1.40  tff(c_551, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_547, c_547, c_250])).
% 2.88/1.40  tff(c_710, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_613, c_613, c_551])).
% 2.88/1.40  tff(c_620, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_613, c_547])).
% 2.88/1.40  tff(c_12, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.88/1.40  tff(c_24, plain, (![C_15, B_14]: (v1_funct_2(C_15, k1_xboole_0, B_14) | k1_relset_1(k1_xboole_0, B_14, C_15)!=k1_xboole_0 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.88/1.40  tff(c_56, plain, (![C_15, B_14]: (v1_funct_2(C_15, k1_xboole_0, B_14) | k1_relset_1(k1_xboole_0, B_14, C_15)!=k1_xboole_0 | ~m1_subset_1(C_15, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_24])).
% 2.88/1.40  tff(c_786, plain, (![C_82, B_83]: (v1_funct_2(C_82, '#skF_3', B_83) | k1_relset_1('#skF_3', B_83, C_82)!='#skF_3' | ~m1_subset_1(C_82, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_620, c_620, c_620, c_620, c_56])).
% 2.88/1.40  tff(c_954, plain, (![B_101]: (v1_funct_2('#skF_3', '#skF_3', B_101) | k1_relset_1('#skF_3', B_101, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_710, c_786])).
% 2.88/1.40  tff(c_624, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_613, c_54])).
% 2.88/1.40  tff(c_957, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_954, c_624])).
% 2.88/1.40  tff(c_966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_623, c_957])).
% 2.88/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.40  
% 2.88/1.40  Inference rules
% 2.88/1.40  ----------------------
% 2.88/1.40  #Ref     : 0
% 2.88/1.40  #Sup     : 201
% 2.88/1.40  #Fact    : 0
% 2.88/1.40  #Define  : 0
% 2.88/1.40  #Split   : 5
% 2.88/1.40  #Chain   : 0
% 2.88/1.40  #Close   : 0
% 2.88/1.40  
% 2.88/1.40  Ordering : KBO
% 2.88/1.40  
% 2.88/1.40  Simplification rules
% 2.88/1.40  ----------------------
% 2.88/1.40  #Subsume      : 16
% 2.88/1.40  #Demod        : 287
% 2.88/1.40  #Tautology    : 137
% 2.88/1.40  #SimpNegUnit  : 2
% 2.88/1.40  #BackRed      : 63
% 2.88/1.40  
% 2.88/1.40  #Partial instantiations: 0
% 2.88/1.40  #Strategies tried      : 1
% 2.88/1.40  
% 2.88/1.40  Timing (in seconds)
% 2.88/1.40  ----------------------
% 2.88/1.40  Preprocessing        : 0.30
% 2.88/1.40  Parsing              : 0.16
% 2.88/1.40  CNF conversion       : 0.02
% 2.88/1.40  Main loop            : 0.35
% 2.88/1.40  Inferencing          : 0.11
% 2.88/1.40  Reduction            : 0.13
% 2.88/1.40  Demodulation         : 0.09
% 2.88/1.40  BG Simplification    : 0.02
% 2.88/1.40  Subsumption          : 0.05
% 2.88/1.40  Abstraction          : 0.02
% 2.88/1.40  MUC search           : 0.00
% 2.88/1.40  Cooper               : 0.00
% 2.88/1.40  Total                : 0.68
% 2.88/1.40  Index Insertion      : 0.00
% 2.88/1.40  Index Deletion       : 0.00
% 2.88/1.40  Index Matching       : 0.00
% 2.88/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
