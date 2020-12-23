%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:20 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 486 expanded)
%              Number of leaves         :   32 ( 184 expanded)
%              Depth                    :   14
%              Number of atoms          :  153 (1535 expanded)
%              Number of equality atoms :   50 ( 525 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ! [C] :
                  ( m1_subset_1(C,A)
                 => k3_funct_2(A,A,B,C) = C )
             => r2_funct_2(A,A,B,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_78,axiom,(
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

tff(f_93,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_85,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_94,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_85])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_50,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_104,plain,(
    ! [A_47,B_48,C_49] :
      ( k1_relset_1(A_47,B_48,C_49) = k1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_113,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_104])).

tff(c_149,plain,(
    ! [B_60,A_61,C_62] :
      ( k1_xboole_0 = B_60
      | k1_relset_1(A_61,B_60,C_62) = A_61
      | ~ v1_funct_2(C_62,A_61,B_60)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_156,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_149])).

tff(c_160,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_113,c_156])).

tff(c_161,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_38,plain,(
    ! [A_21] : k6_relat_1(A_21) = k6_partfun1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_4),B_4),k1_relat_1(B_4))
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_57,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_4),B_4),k1_relat_1(B_4))
      | k6_partfun1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_14])).

tff(c_166,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),k1_relat_1('#skF_3'))
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_57])).

tff(c_173,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_52,c_161,c_161,c_166])).

tff(c_181,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_44,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_182,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_44])).

tff(c_223,plain,(
    ! [A_68,B_69,D_70] :
      ( r2_funct_2(A_68,B_69,D_70,D_70)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ v1_funct_2(D_70,A_68,B_69)
      | ~ v1_funct_1(D_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_228,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_223])).

tff(c_232,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_228])).

tff(c_234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_232])).

tff(c_236,plain,(
    k6_partfun1('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_12,plain,(
    ! [B_4] :
      ( k1_funct_1(B_4,'#skF_1'(k1_relat_1(B_4),B_4)) != '#skF_1'(k1_relat_1(B_4),B_4)
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_282,plain,(
    ! [B_77] :
      ( k1_funct_1(B_77,'#skF_1'(k1_relat_1(B_77),B_77)) != '#skF_1'(k1_relat_1(B_77),B_77)
      | k6_partfun1(k1_relat_1(B_77)) = B_77
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12])).

tff(c_285,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_282])).

tff(c_287,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_52,c_161,c_161,c_285])).

tff(c_288,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_287])).

tff(c_169,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_3'),'#skF_3'),'#skF_2')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_57])).

tff(c_175,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_52,c_161,c_161,c_169])).

tff(c_237,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_237])).

tff(c_239,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( m1_subset_1(B_2,A_1)
      | ~ r2_hidden(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_243,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_239,c_4])).

tff(c_246,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_243])).

tff(c_46,plain,(
    ! [C_30] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_30) = C_30
      | ~ m1_subset_1(C_30,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_266,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_246,c_46])).

tff(c_306,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k3_funct_2(A_79,B_80,C_81,D_82) = k1_funct_1(C_81,D_82)
      | ~ m1_subset_1(D_82,A_79)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_2(C_81,A_79,B_80)
      | ~ v1_funct_1(C_81)
      | v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_310,plain,(
    ! [B_80,C_81] :
      ( k3_funct_2('#skF_2',B_80,C_81,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_81,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_80)))
      | ~ v1_funct_2(C_81,'#skF_2',B_80)
      | ~ v1_funct_1(C_81)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_246,c_306])).

tff(c_330,plain,(
    ! [B_87,C_88] :
      ( k3_funct_2('#skF_2',B_87,C_88,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_88,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_87)))
      | ~ v1_funct_2(C_88,'#skF_2',B_87)
      | ~ v1_funct_1(C_88) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_310])).

tff(c_337,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_330])).

tff(c_341,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_266,c_337])).

tff(c_343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_341])).

tff(c_344,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_351,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_2])).

tff(c_353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_351])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.45  
% 2.46/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.45  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.46/1.45  
% 2.46/1.45  %Foreground sorts:
% 2.46/1.45  
% 2.46/1.45  
% 2.46/1.45  %Background operators:
% 2.46/1.45  
% 2.46/1.45  
% 2.46/1.45  %Foreground operators:
% 2.46/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.46/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.46/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.46/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.46/1.45  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.46/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.46/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.46/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.46/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.46/1.45  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.46/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.46/1.45  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.46/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.45  
% 2.85/1.47  tff(f_127, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_funct_2)).
% 2.85/1.47  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.85/1.47  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.85/1.47  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.85/1.47  tff(f_93, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.85/1.47  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.85/1.47  tff(f_109, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.85/1.47  tff(f_39, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.85/1.47  tff(f_91, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.85/1.47  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.85/1.47  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.85/1.47  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.85/1.47  tff(c_85, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.85/1.47  tff(c_94, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_85])).
% 2.85/1.47  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.85/1.47  tff(c_50, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.85/1.47  tff(c_104, plain, (![A_47, B_48, C_49]: (k1_relset_1(A_47, B_48, C_49)=k1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.85/1.47  tff(c_113, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_104])).
% 2.85/1.47  tff(c_149, plain, (![B_60, A_61, C_62]: (k1_xboole_0=B_60 | k1_relset_1(A_61, B_60, C_62)=A_61 | ~v1_funct_2(C_62, A_61, B_60) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.85/1.47  tff(c_156, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_149])).
% 2.85/1.47  tff(c_160, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_113, c_156])).
% 2.85/1.47  tff(c_161, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitLeft, [status(thm)], [c_160])).
% 2.85/1.47  tff(c_38, plain, (![A_21]: (k6_relat_1(A_21)=k6_partfun1(A_21))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.85/1.47  tff(c_14, plain, (![B_4]: (r2_hidden('#skF_1'(k1_relat_1(B_4), B_4), k1_relat_1(B_4)) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.85/1.47  tff(c_57, plain, (![B_4]: (r2_hidden('#skF_1'(k1_relat_1(B_4), B_4), k1_relat_1(B_4)) | k6_partfun1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_14])).
% 2.85/1.47  tff(c_166, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), k1_relat_1('#skF_3')) | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_161, c_57])).
% 2.85/1.47  tff(c_173, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_52, c_161, c_161, c_166])).
% 2.85/1.47  tff(c_181, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_173])).
% 2.85/1.47  tff(c_44, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.85/1.47  tff(c_182, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_44])).
% 2.85/1.47  tff(c_223, plain, (![A_68, B_69, D_70]: (r2_funct_2(A_68, B_69, D_70, D_70) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~v1_funct_2(D_70, A_68, B_69) | ~v1_funct_1(D_70))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.85/1.47  tff(c_228, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_223])).
% 2.85/1.47  tff(c_232, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_228])).
% 2.85/1.47  tff(c_234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_232])).
% 2.85/1.47  tff(c_236, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_173])).
% 2.85/1.47  tff(c_12, plain, (![B_4]: (k1_funct_1(B_4, '#skF_1'(k1_relat_1(B_4), B_4))!='#skF_1'(k1_relat_1(B_4), B_4) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.85/1.47  tff(c_282, plain, (![B_77]: (k1_funct_1(B_77, '#skF_1'(k1_relat_1(B_77), B_77))!='#skF_1'(k1_relat_1(B_77), B_77) | k6_partfun1(k1_relat_1(B_77))=B_77 | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12])).
% 2.85/1.47  tff(c_285, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_161, c_282])).
% 2.85/1.47  tff(c_287, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_52, c_161, c_161, c_285])).
% 2.85/1.47  tff(c_288, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_236, c_287])).
% 2.85/1.47  tff(c_169, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_3'), '#skF_3'), '#skF_2') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_161, c_57])).
% 2.85/1.47  tff(c_175, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_52, c_161, c_161, c_169])).
% 2.85/1.47  tff(c_237, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_175])).
% 2.85/1.47  tff(c_238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_237])).
% 2.85/1.47  tff(c_239, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_175])).
% 2.85/1.47  tff(c_4, plain, (![B_2, A_1]: (m1_subset_1(B_2, A_1) | ~r2_hidden(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.85/1.47  tff(c_243, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_239, c_4])).
% 2.85/1.47  tff(c_246, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_243])).
% 2.85/1.47  tff(c_46, plain, (![C_30]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_30)=C_30 | ~m1_subset_1(C_30, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.85/1.47  tff(c_266, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_246, c_46])).
% 2.85/1.47  tff(c_306, plain, (![A_79, B_80, C_81, D_82]: (k3_funct_2(A_79, B_80, C_81, D_82)=k1_funct_1(C_81, D_82) | ~m1_subset_1(D_82, A_79) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_2(C_81, A_79, B_80) | ~v1_funct_1(C_81) | v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.85/1.47  tff(c_310, plain, (![B_80, C_81]: (k3_funct_2('#skF_2', B_80, C_81, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_81, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_80))) | ~v1_funct_2(C_81, '#skF_2', B_80) | ~v1_funct_1(C_81) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_246, c_306])).
% 2.85/1.47  tff(c_330, plain, (![B_87, C_88]: (k3_funct_2('#skF_2', B_87, C_88, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_88, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_87))) | ~v1_funct_2(C_88, '#skF_2', B_87) | ~v1_funct_1(C_88))), inference(negUnitSimplification, [status(thm)], [c_54, c_310])).
% 2.85/1.47  tff(c_337, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_330])).
% 2.85/1.47  tff(c_341, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_266, c_337])).
% 2.85/1.47  tff(c_343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_288, c_341])).
% 2.85/1.47  tff(c_344, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_160])).
% 2.85/1.47  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.85/1.47  tff(c_351, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_344, c_2])).
% 2.85/1.47  tff(c_353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_351])).
% 2.85/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.47  
% 2.85/1.47  Inference rules
% 2.85/1.47  ----------------------
% 2.85/1.47  #Ref     : 0
% 2.85/1.47  #Sup     : 55
% 2.85/1.47  #Fact    : 0
% 2.85/1.47  #Define  : 0
% 2.85/1.47  #Split   : 5
% 2.85/1.47  #Chain   : 0
% 2.85/1.47  #Close   : 0
% 2.85/1.47  
% 2.85/1.47  Ordering : KBO
% 2.85/1.47  
% 2.85/1.47  Simplification rules
% 2.85/1.47  ----------------------
% 2.85/1.47  #Subsume      : 16
% 2.85/1.47  #Demod        : 81
% 2.85/1.47  #Tautology    : 24
% 2.85/1.47  #SimpNegUnit  : 11
% 2.85/1.47  #BackRed      : 8
% 2.85/1.47  
% 2.85/1.47  #Partial instantiations: 0
% 2.85/1.47  #Strategies tried      : 1
% 2.85/1.47  
% 2.85/1.47  Timing (in seconds)
% 2.85/1.47  ----------------------
% 2.85/1.47  Preprocessing        : 0.36
% 2.85/1.47  Parsing              : 0.18
% 2.85/1.47  CNF conversion       : 0.02
% 2.85/1.47  Main loop            : 0.32
% 2.85/1.47  Inferencing          : 0.10
% 2.85/1.47  Reduction            : 0.11
% 2.85/1.47  Demodulation         : 0.07
% 2.85/1.47  BG Simplification    : 0.02
% 2.85/1.47  Subsumption          : 0.06
% 2.85/1.47  Abstraction          : 0.02
% 2.85/1.47  MUC search           : 0.00
% 2.85/1.47  Cooper               : 0.00
% 2.85/1.47  Total                : 0.72
% 2.85/1.47  Index Insertion      : 0.00
% 2.85/1.47  Index Deletion       : 0.00
% 2.85/1.47  Index Matching       : 0.00
% 2.85/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
