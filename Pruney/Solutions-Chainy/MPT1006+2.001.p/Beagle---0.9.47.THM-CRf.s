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
% DateTime   : Thu Dec  3 10:14:02 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 539 expanded)
%              Number of leaves         :   32 ( 197 expanded)
%              Depth                    :   12
%              Number of atoms          :  105 ( 846 expanded)
%              Number of equality atoms :   37 ( 302 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_97,axiom,(
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

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [A_31] :
      ( k1_xboole_0 = A_31
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_78])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_51,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_44])).

tff(c_87,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_51])).

tff(c_125,plain,(
    ! [B_37,A_38] :
      ( v1_xboole_0(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_131,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_87,c_125])).

tff(c_136,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_131])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2])).

tff(c_140,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_136,c_83])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    ! [A_4] : m1_subset_1('#skF_1',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_12])).

tff(c_141,plain,(
    ! [A_4] : m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_84])).

tff(c_88,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_10])).

tff(c_146,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_140,c_88])).

tff(c_213,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_partfun1(C_51,A_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_219,plain,(
    ! [C_51] :
      ( v1_partfun1(C_51,'#skF_4')
      | ~ m1_subset_1(C_51,k1_zfmisc_1('#skF_4'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_213])).

tff(c_228,plain,(
    ! [C_55] :
      ( v1_partfun1(C_55,'#skF_4')
      | ~ m1_subset_1(C_55,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_219])).

tff(c_233,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_228])).

tff(c_284,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( k8_relset_1(A_65,B_66,C_67,D_68) = k10_relat_1(C_67,D_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_292,plain,(
    ! [A_65,B_66,D_68] : k8_relset_1(A_65,B_66,'#skF_4',D_68) = k10_relat_1('#skF_4',D_68) ),
    inference(resolution,[status(thm)],[c_141,c_284])).

tff(c_303,plain,(
    ! [A_72,B_73,C_74] :
      ( k8_relset_1(A_72,B_73,C_74,B_73) = k1_relset_1(A_72,B_73,C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_310,plain,(
    ! [A_72,B_73] : k8_relset_1(A_72,B_73,'#skF_4',B_73) = k1_relset_1(A_72,B_73,'#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_303])).

tff(c_312,plain,(
    ! [A_72,B_73] : k1_relset_1(A_72,B_73,'#skF_4') = k10_relat_1('#skF_4',B_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_310])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_334,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_funct_2(C_77,A_78,B_79)
      | ~ v1_partfun1(C_77,A_78)
      | ~ v1_funct_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_344,plain,(
    ! [A_78,B_79] :
      ( v1_funct_2('#skF_4',A_78,B_79)
      | ~ v1_partfun1('#skF_4',A_78)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_141,c_334])).

tff(c_348,plain,(
    ! [A_80,B_81] :
      ( v1_funct_2('#skF_4',A_80,B_81)
      | ~ v1_partfun1('#skF_4',A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_344])).

tff(c_149,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_82])).

tff(c_38,plain,(
    ! [B_26,C_27] :
      ( k1_relset_1(k1_xboole_0,B_26,C_27) = k1_xboole_0
      | ~ v1_funct_2(C_27,k1_xboole_0,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,(
    ! [B_26,C_27] :
      ( k1_relset_1(k1_xboole_0,B_26,C_27) = k1_xboole_0
      | ~ v1_funct_2(C_27,k1_xboole_0,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_38])).

tff(c_247,plain,(
    ! [B_26,C_27] :
      ( k1_relset_1('#skF_4',B_26,C_27) = '#skF_4'
      | ~ v1_funct_2(C_27,'#skF_4',B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_149,c_149,c_149,c_52])).

tff(c_351,plain,(
    ! [B_81] :
      ( k1_relset_1('#skF_4',B_81,'#skF_4') = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
      | ~ v1_partfun1('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_348,c_247])).

tff(c_357,plain,(
    ! [B_81] : k10_relat_1('#skF_4',B_81) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_141,c_312,c_351])).

tff(c_42,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_93,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_4','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_42])).

tff(c_148,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_140,c_93])).

tff(c_293,plain,(
    k10_relat_1('#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_148])).

tff(c_367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n020.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 11:14:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.26  
% 2.20/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.26  %$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.20/1.26  
% 2.20/1.26  %Foreground sorts:
% 2.20/1.26  
% 2.20/1.26  
% 2.20/1.26  %Background operators:
% 2.20/1.26  
% 2.20/1.26  
% 2.20/1.26  %Foreground operators:
% 2.20/1.26  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.20/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.20/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.26  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.20/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.26  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.20/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.20/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.26  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.20/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.20/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.26  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.20/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.20/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.26  
% 2.20/1.28  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.20/1.28  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.20/1.28  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.20/1.28  tff(f_106, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.20/1.28  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.20/1.28  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.20/1.28  tff(f_79, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 2.20/1.28  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.20/1.28  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.20/1.28  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 2.20/1.28  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.20/1.28  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.28  tff(c_78, plain, (![A_31]: (k1_xboole_0=A_31 | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.28  tff(c_82, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_78])).
% 2.20/1.28  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.20/1.28  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.20/1.28  tff(c_51, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_44])).
% 2.20/1.28  tff(c_87, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_51])).
% 2.20/1.28  tff(c_125, plain, (![B_37, A_38]: (v1_xboole_0(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.20/1.28  tff(c_131, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_87, c_125])).
% 2.20/1.28  tff(c_136, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_131])).
% 2.20/1.28  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.28  tff(c_83, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2])).
% 2.20/1.28  tff(c_140, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_136, c_83])).
% 2.20/1.28  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.28  tff(c_84, plain, (![A_4]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_12])).
% 2.20/1.28  tff(c_141, plain, (![A_4]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_84])).
% 2.20/1.28  tff(c_88, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_10])).
% 2.20/1.28  tff(c_146, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_140, c_88])).
% 2.20/1.28  tff(c_213, plain, (![C_51, A_52, B_53]: (v1_partfun1(C_51, A_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.20/1.28  tff(c_219, plain, (![C_51]: (v1_partfun1(C_51, '#skF_4') | ~m1_subset_1(C_51, k1_zfmisc_1('#skF_4')) | ~v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_213])).
% 2.20/1.28  tff(c_228, plain, (![C_55]: (v1_partfun1(C_55, '#skF_4') | ~m1_subset_1(C_55, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_219])).
% 2.20/1.28  tff(c_233, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_141, c_228])).
% 2.20/1.28  tff(c_284, plain, (![A_65, B_66, C_67, D_68]: (k8_relset_1(A_65, B_66, C_67, D_68)=k10_relat_1(C_67, D_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.20/1.28  tff(c_292, plain, (![A_65, B_66, D_68]: (k8_relset_1(A_65, B_66, '#skF_4', D_68)=k10_relat_1('#skF_4', D_68))), inference(resolution, [status(thm)], [c_141, c_284])).
% 2.20/1.28  tff(c_303, plain, (![A_72, B_73, C_74]: (k8_relset_1(A_72, B_73, C_74, B_73)=k1_relset_1(A_72, B_73, C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.20/1.28  tff(c_310, plain, (![A_72, B_73]: (k8_relset_1(A_72, B_73, '#skF_4', B_73)=k1_relset_1(A_72, B_73, '#skF_4'))), inference(resolution, [status(thm)], [c_141, c_303])).
% 2.20/1.28  tff(c_312, plain, (![A_72, B_73]: (k1_relset_1(A_72, B_73, '#skF_4')=k10_relat_1('#skF_4', B_73))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_310])).
% 2.37/1.28  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.37/1.28  tff(c_334, plain, (![C_77, A_78, B_79]: (v1_funct_2(C_77, A_78, B_79) | ~v1_partfun1(C_77, A_78) | ~v1_funct_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.37/1.28  tff(c_344, plain, (![A_78, B_79]: (v1_funct_2('#skF_4', A_78, B_79) | ~v1_partfun1('#skF_4', A_78) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_141, c_334])).
% 2.37/1.28  tff(c_348, plain, (![A_80, B_81]: (v1_funct_2('#skF_4', A_80, B_81) | ~v1_partfun1('#skF_4', A_80))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_344])).
% 2.37/1.28  tff(c_149, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_82])).
% 2.37/1.28  tff(c_38, plain, (![B_26, C_27]: (k1_relset_1(k1_xboole_0, B_26, C_27)=k1_xboole_0 | ~v1_funct_2(C_27, k1_xboole_0, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.37/1.28  tff(c_52, plain, (![B_26, C_27]: (k1_relset_1(k1_xboole_0, B_26, C_27)=k1_xboole_0 | ~v1_funct_2(C_27, k1_xboole_0, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_38])).
% 2.37/1.28  tff(c_247, plain, (![B_26, C_27]: (k1_relset_1('#skF_4', B_26, C_27)='#skF_4' | ~v1_funct_2(C_27, '#skF_4', B_26) | ~m1_subset_1(C_27, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_149, c_149, c_149, c_52])).
% 2.37/1.28  tff(c_351, plain, (![B_81]: (k1_relset_1('#skF_4', B_81, '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_partfun1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_348, c_247])).
% 2.37/1.28  tff(c_357, plain, (![B_81]: (k10_relat_1('#skF_4', B_81)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_233, c_141, c_312, c_351])).
% 2.37/1.28  tff(c_42, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.37/1.28  tff(c_93, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_42])).
% 2.37/1.28  tff(c_148, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_140, c_93])).
% 2.37/1.28  tff(c_293, plain, (k10_relat_1('#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_292, c_148])).
% 2.37/1.28  tff(c_367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_357, c_293])).
% 2.37/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.28  
% 2.37/1.28  Inference rules
% 2.37/1.28  ----------------------
% 2.37/1.28  #Ref     : 0
% 2.37/1.28  #Sup     : 66
% 2.37/1.28  #Fact    : 0
% 2.37/1.28  #Define  : 0
% 2.37/1.28  #Split   : 0
% 2.37/1.28  #Chain   : 0
% 2.37/1.28  #Close   : 0
% 2.37/1.28  
% 2.37/1.28  Ordering : KBO
% 2.37/1.28  
% 2.37/1.28  Simplification rules
% 2.37/1.28  ----------------------
% 2.37/1.28  #Subsume      : 1
% 2.37/1.28  #Demod        : 72
% 2.37/1.28  #Tautology    : 48
% 2.37/1.28  #SimpNegUnit  : 0
% 2.37/1.28  #BackRed      : 21
% 2.37/1.28  
% 2.37/1.28  #Partial instantiations: 0
% 2.37/1.28  #Strategies tried      : 1
% 2.37/1.28  
% 2.37/1.28  Timing (in seconds)
% 2.37/1.28  ----------------------
% 2.37/1.28  Preprocessing        : 0.32
% 2.37/1.28  Parsing              : 0.17
% 2.37/1.28  CNF conversion       : 0.02
% 2.37/1.28  Main loop            : 0.21
% 2.37/1.28  Inferencing          : 0.07
% 2.37/1.28  Reduction            : 0.07
% 2.37/1.28  Demodulation         : 0.05
% 2.37/1.28  BG Simplification    : 0.02
% 2.37/1.28  Subsumption          : 0.04
% 2.37/1.28  Abstraction          : 0.01
% 2.37/1.28  MUC search           : 0.00
% 2.37/1.28  Cooper               : 0.00
% 2.37/1.28  Total                : 0.57
% 2.37/1.28  Index Insertion      : 0.00
% 2.37/1.28  Index Deletion       : 0.00
% 2.37/1.28  Index Matching       : 0.00
% 2.37/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
