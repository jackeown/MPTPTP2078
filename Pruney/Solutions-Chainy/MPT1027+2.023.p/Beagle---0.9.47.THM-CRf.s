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
% DateTime   : Thu Dec  3 10:16:45 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   90 (2000 expanded)
%              Number of leaves         :   34 ( 735 expanded)
%              Depth                    :   13
%              Number of atoms          :  124 (6349 expanded)
%              Number of equality atoms :   45 (2157 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_69,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_59,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_62,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_funct_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

tff(c_60,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_495,plain,(
    ! [A_70,B_71,C_72] :
      ( k1_relset_1(A_70,B_71,C_72) = k1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_498,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_495])).

tff(c_510,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_498])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_58,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_66,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58])).

tff(c_626,plain,(
    ! [B_83,C_84,A_85] :
      ( k1_xboole_0 = B_83
      | v1_funct_2(C_84,A_85,B_83)
      | k1_relset_1(A_85,B_83,C_84) != A_85
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_635,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_62,c_626])).

tff(c_652,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_635])).

tff(c_653,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_652])).

tff(c_32,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_685,plain,(
    k6_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_653,c_32])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_682,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_653,c_6])).

tff(c_273,plain,(
    ! [A_49,B_50] :
      ( k9_relat_1(k6_relat_1(A_49),B_50) = B_50
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_280,plain,(
    k9_relat_1(k6_relat_1(k2_zfmisc_1('#skF_1','#skF_2')),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_62,c_273])).

tff(c_781,plain,(
    k9_relat_1(k6_relat_1('#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_280])).

tff(c_783,plain,(
    k9_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_781])).

tff(c_22,plain,(
    ! [A_14] : k9_relat_1(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_678,plain,(
    ! [A_14] : k9_relat_1('#skF_2',A_14) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_653,c_22])).

tff(c_814,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_678])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_684,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_653,c_26])).

tff(c_853,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_814,c_684])).

tff(c_862,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_853])).

tff(c_870,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_814])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_111,plain,(
    ! [A_31,B_32] : v1_relat_1(k2_zfmisc_1(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_113,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_111])).

tff(c_679,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_113])).

tff(c_20,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_148,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_151,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_148])).

tff(c_157,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_151])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_296,plain,(
    ! [A_52] :
      ( v1_funct_2(A_52,k1_relat_1(A_52),k2_relat_1(A_52))
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_299,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_296])).

tff(c_304,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_26,c_299])).

tff(c_307,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_10,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_308,plain,(
    ! [B_53,A_54] :
      ( v1_funct_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_314,plain,(
    ! [A_3] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(resolution,[status(thm)],[c_10,c_308])).

tff(c_321,plain,(
    ! [A_55] :
      ( ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_314])).

tff(c_327,plain,(
    ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_157,c_321])).

tff(c_338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_327])).

tff(c_340,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_667,plain,(
    v1_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_340])).

tff(c_683,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_653,c_24])).

tff(c_54,plain,(
    ! [A_27] :
      ( v1_funct_2(A_27,k1_relat_1(A_27),k2_relat_1(A_27))
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_713,plain,
    ( v1_funct_2('#skF_2','#skF_2',k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_684,c_54])).

tff(c_719,plain,(
    v1_funct_2('#skF_2','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_667,c_683,c_713])).

tff(c_948,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_870,c_870,c_719])).

tff(c_861,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_66])).

tff(c_955,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_948,c_862,c_862,c_861])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:15:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.43  
% 2.72/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.44  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.72/1.44  
% 2.72/1.44  %Foreground sorts:
% 2.72/1.44  
% 2.72/1.44  
% 2.72/1.44  %Background operators:
% 2.72/1.44  
% 2.72/1.44  
% 2.72/1.44  %Foreground operators:
% 2.72/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.72/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.72/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.72/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.72/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.72/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.72/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.72/1.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.72/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.72/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.72/1.44  
% 2.72/1.45  tff(f_127, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 2.72/1.45  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.72/1.45  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.72/1.45  tff(f_69, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.72/1.45  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.72/1.45  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.72/1.45  tff(f_59, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.72/1.45  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.72/1.45  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.72/1.45  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.72/1.45  tff(f_114, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 2.72/1.45  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.72/1.45  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_funct_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 2.72/1.45  tff(c_60, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.72/1.45  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.72/1.45  tff(c_495, plain, (![A_70, B_71, C_72]: (k1_relset_1(A_70, B_71, C_72)=k1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.72/1.45  tff(c_498, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_495])).
% 2.72/1.45  tff(c_510, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_498])).
% 2.72/1.45  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.72/1.45  tff(c_58, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.72/1.45  tff(c_66, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58])).
% 2.72/1.45  tff(c_626, plain, (![B_83, C_84, A_85]: (k1_xboole_0=B_83 | v1_funct_2(C_84, A_85, B_83) | k1_relset_1(A_85, B_83, C_84)!=A_85 | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_83))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.72/1.45  tff(c_635, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_62, c_626])).
% 2.72/1.45  tff(c_652, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_635])).
% 2.72/1.45  tff(c_653, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_66, c_652])).
% 2.72/1.45  tff(c_32, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.72/1.45  tff(c_685, plain, (k6_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_653, c_653, c_32])).
% 2.72/1.45  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.45  tff(c_682, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_653, c_653, c_6])).
% 2.72/1.45  tff(c_273, plain, (![A_49, B_50]: (k9_relat_1(k6_relat_1(A_49), B_50)=B_50 | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.72/1.45  tff(c_280, plain, (k9_relat_1(k6_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_62, c_273])).
% 2.72/1.45  tff(c_781, plain, (k9_relat_1(k6_relat_1('#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_682, c_280])).
% 2.72/1.45  tff(c_783, plain, (k9_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_685, c_781])).
% 2.72/1.45  tff(c_22, plain, (![A_14]: (k9_relat_1(k1_xboole_0, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.72/1.45  tff(c_678, plain, (![A_14]: (k9_relat_1('#skF_2', A_14)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_653, c_653, c_22])).
% 2.72/1.45  tff(c_814, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_783, c_678])).
% 2.72/1.45  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.72/1.45  tff(c_684, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_653, c_653, c_26])).
% 2.72/1.45  tff(c_853, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_814, c_814, c_684])).
% 2.72/1.45  tff(c_862, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_510, c_853])).
% 2.72/1.45  tff(c_870, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_862, c_814])).
% 2.72/1.45  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.45  tff(c_111, plain, (![A_31, B_32]: (v1_relat_1(k2_zfmisc_1(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.72/1.45  tff(c_113, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_111])).
% 2.72/1.45  tff(c_679, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_653, c_113])).
% 2.72/1.45  tff(c_20, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.72/1.45  tff(c_148, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.72/1.45  tff(c_151, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_148])).
% 2.72/1.45  tff(c_157, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_151])).
% 2.72/1.45  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.72/1.45  tff(c_296, plain, (![A_52]: (v1_funct_2(A_52, k1_relat_1(A_52), k2_relat_1(A_52)) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.72/1.45  tff(c_299, plain, (v1_funct_2(k1_xboole_0, k1_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_296])).
% 2.72/1.45  tff(c_304, plain, (v1_funct_2(k1_xboole_0, k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_113, c_26, c_299])).
% 2.72/1.45  tff(c_307, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_304])).
% 2.72/1.45  tff(c_10, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.72/1.45  tff(c_308, plain, (![B_53, A_54]: (v1_funct_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.72/1.45  tff(c_314, plain, (![A_3]: (v1_funct_1(k1_xboole_0) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(resolution, [status(thm)], [c_10, c_308])).
% 2.72/1.45  tff(c_321, plain, (![A_55]: (~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(negUnitSimplification, [status(thm)], [c_307, c_314])).
% 2.72/1.45  tff(c_327, plain, (~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_157, c_321])).
% 2.72/1.45  tff(c_338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_327])).
% 2.72/1.45  tff(c_340, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_304])).
% 2.72/1.45  tff(c_667, plain, (v1_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_653, c_340])).
% 2.72/1.45  tff(c_683, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_653, c_653, c_24])).
% 2.72/1.45  tff(c_54, plain, (![A_27]: (v1_funct_2(A_27, k1_relat_1(A_27), k2_relat_1(A_27)) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.72/1.45  tff(c_713, plain, (v1_funct_2('#skF_2', '#skF_2', k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_684, c_54])).
% 2.72/1.45  tff(c_719, plain, (v1_funct_2('#skF_2', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_679, c_667, c_683, c_713])).
% 2.72/1.45  tff(c_948, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_870, c_870, c_870, c_719])).
% 2.72/1.45  tff(c_861, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_814, c_66])).
% 2.72/1.45  tff(c_955, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_948, c_862, c_862, c_861])).
% 2.72/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.45  
% 2.72/1.45  Inference rules
% 2.72/1.45  ----------------------
% 2.72/1.45  #Ref     : 0
% 2.72/1.45  #Sup     : 202
% 2.72/1.45  #Fact    : 0
% 2.72/1.45  #Define  : 0
% 2.72/1.45  #Split   : 1
% 2.72/1.45  #Chain   : 0
% 2.72/1.45  #Close   : 0
% 2.72/1.45  
% 2.72/1.45  Ordering : KBO
% 2.72/1.45  
% 2.72/1.45  Simplification rules
% 2.72/1.45  ----------------------
% 2.72/1.45  #Subsume      : 4
% 2.72/1.45  #Demod        : 308
% 2.72/1.45  #Tautology    : 150
% 2.72/1.45  #SimpNegUnit  : 2
% 2.72/1.45  #BackRed      : 60
% 2.72/1.45  
% 2.72/1.45  #Partial instantiations: 0
% 2.72/1.45  #Strategies tried      : 1
% 2.72/1.45  
% 2.72/1.45  Timing (in seconds)
% 2.72/1.45  ----------------------
% 2.72/1.45  Preprocessing        : 0.33
% 2.72/1.45  Parsing              : 0.17
% 2.72/1.45  CNF conversion       : 0.02
% 2.72/1.46  Main loop            : 0.35
% 2.72/1.46  Inferencing          : 0.11
% 2.72/1.46  Reduction            : 0.13
% 2.72/1.46  Demodulation         : 0.09
% 2.72/1.46  BG Simplification    : 0.02
% 2.72/1.46  Subsumption          : 0.06
% 2.72/1.46  Abstraction          : 0.02
% 2.72/1.46  MUC search           : 0.00
% 2.72/1.46  Cooper               : 0.00
% 2.72/1.46  Total                : 0.71
% 2.72/1.46  Index Insertion      : 0.00
% 2.72/1.46  Index Deletion       : 0.00
% 2.72/1.46  Index Matching       : 0.00
% 2.72/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
