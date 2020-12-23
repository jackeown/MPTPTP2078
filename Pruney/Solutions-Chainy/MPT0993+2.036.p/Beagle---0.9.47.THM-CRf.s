%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:47 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 157 expanded)
%              Number of leaves         :   33 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 366 expanded)
%              Number of equality atoms :   39 (  88 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_94,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_155,plain,(
    ! [A_57,B_58,D_59] :
      ( r2_relset_1(A_57,B_58,D_59,D_59)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_162,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_155])).

tff(c_48,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_16,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_111,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_114,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_111])).

tff(c_117,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_114])).

tff(c_185,plain,(
    ! [D_77,B_78,C_79,A_80] :
      ( m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(B_78,C_79)))
      | ~ r1_tarski(k1_relat_1(D_77),B_78)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_80,C_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_192,plain,(
    ! [B_78] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_78,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_78) ) ),
    inference(resolution,[status(thm)],[c_50,c_185])).

tff(c_296,plain,(
    ! [B_93,C_94,A_95] :
      ( k1_xboole_0 = B_93
      | v1_funct_2(C_94,A_95,B_93)
      | k1_relset_1(A_95,B_93,C_94) != A_95
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_309,plain,(
    ! [B_78] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2('#skF_4',B_78,'#skF_2')
      | k1_relset_1(B_78,'#skF_2','#skF_4') != B_78
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_78) ) ),
    inference(resolution,[status(thm)],[c_192,c_296])).

tff(c_357,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_373,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_357,c_10])).

tff(c_381,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_50])).

tff(c_132,plain,(
    ! [C_52,A_53,B_54] :
      ( v4_relat_1(C_52,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_138,plain,(
    ! [C_52,A_3] :
      ( v4_relat_1(C_52,A_3)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_132])).

tff(c_463,plain,(
    ! [C_108,A_109] :
      ( v4_relat_1(C_108,A_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_138])).

tff(c_470,plain,(
    ! [A_110] : v4_relat_1('#skF_4',A_110) ),
    inference(resolution,[status(thm)],[c_381,c_463])).

tff(c_18,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_473,plain,(
    ! [A_110] :
      ( k7_relat_1('#skF_4',A_110) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_470,c_18])).

tff(c_476,plain,(
    ! [A_110] : k7_relat_1('#skF_4',A_110) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_473])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_241,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( k2_partfun1(A_83,B_84,C_85,D_86) = k7_relat_1(C_85,D_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_245,plain,(
    ! [D_86] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_86) = k7_relat_1('#skF_4',D_86)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_241])).

tff(c_255,plain,(
    ! [D_86] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_86) = k7_relat_1('#skF_4',D_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_245])).

tff(c_46,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_256,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_46])).

tff(c_479,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_256])).

tff(c_485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_479])).

tff(c_487,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_52,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_166,plain,(
    ! [A_66,B_67,C_68] :
      ( k1_relset_1(A_66,B_67,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_176,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_166])).

tff(c_493,plain,(
    ! [B_114,A_115,C_116] :
      ( k1_xboole_0 = B_114
      | k1_relset_1(A_115,B_114,C_116) = A_115
      | ~ v1_funct_2(C_116,A_115,B_114)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_502,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_493])).

tff(c_515,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_176,c_502])).

tff(c_516,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_487,c_515])).

tff(c_194,plain,(
    ! [B_81] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_81,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_81) ) ),
    inference(resolution,[status(thm)],[c_50,c_185])).

tff(c_22,plain,(
    ! [C_14,A_12,B_13] :
      ( v4_relat_1(C_14,A_12)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_218,plain,(
    ! [B_81] :
      ( v4_relat_1('#skF_4',B_81)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_81) ) ),
    inference(resolution,[status(thm)],[c_194,c_22])).

tff(c_594,plain,(
    ! [B_118] :
      ( v4_relat_1('#skF_4',B_118)
      | ~ r1_tarski('#skF_1',B_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_218])).

tff(c_597,plain,(
    ! [B_118] :
      ( k7_relat_1('#skF_4',B_118) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',B_118) ) ),
    inference(resolution,[status(thm)],[c_594,c_18])).

tff(c_601,plain,(
    ! [B_119] :
      ( k7_relat_1('#skF_4',B_119) = '#skF_4'
      | ~ r1_tarski('#skF_1',B_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_597])).

tff(c_611,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_601])).

tff(c_612,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_256])).

tff(c_615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_612])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:31:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.37  
% 2.73/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.37  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.73/1.37  
% 2.73/1.37  %Foreground sorts:
% 2.73/1.37  
% 2.73/1.37  
% 2.73/1.37  %Background operators:
% 2.73/1.37  
% 2.73/1.37  
% 2.73/1.37  %Foreground operators:
% 2.73/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.37  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.73/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.73/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.73/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.73/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.73/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.73/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.37  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.73/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.73/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.37  
% 2.73/1.38  tff(f_111, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 2.73/1.38  tff(f_70, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.73/1.38  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.73/1.38  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.73/1.38  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 2.73/1.38  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.73/1.38  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.73/1.38  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.73/1.38  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.73/1.38  tff(f_100, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.73/1.38  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.73/1.38  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.73/1.38  tff(c_155, plain, (![A_57, B_58, D_59]: (r2_relset_1(A_57, B_58, D_59, D_59) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.73/1.38  tff(c_162, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_155])).
% 2.73/1.38  tff(c_48, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.73/1.38  tff(c_16, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.73/1.38  tff(c_111, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.73/1.38  tff(c_114, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_111])).
% 2.73/1.38  tff(c_117, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_114])).
% 2.73/1.38  tff(c_185, plain, (![D_77, B_78, C_79, A_80]: (m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(B_78, C_79))) | ~r1_tarski(k1_relat_1(D_77), B_78) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_80, C_79))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.73/1.38  tff(c_192, plain, (![B_78]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_78, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_78))), inference(resolution, [status(thm)], [c_50, c_185])).
% 2.73/1.38  tff(c_296, plain, (![B_93, C_94, A_95]: (k1_xboole_0=B_93 | v1_funct_2(C_94, A_95, B_93) | k1_relset_1(A_95, B_93, C_94)!=A_95 | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_93))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.73/1.38  tff(c_309, plain, (![B_78]: (k1_xboole_0='#skF_2' | v1_funct_2('#skF_4', B_78, '#skF_2') | k1_relset_1(B_78, '#skF_2', '#skF_4')!=B_78 | ~r1_tarski(k1_relat_1('#skF_4'), B_78))), inference(resolution, [status(thm)], [c_192, c_296])).
% 2.73/1.38  tff(c_357, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_309])).
% 2.73/1.38  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.38  tff(c_373, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_357, c_10])).
% 2.73/1.38  tff(c_381, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_373, c_50])).
% 2.73/1.38  tff(c_132, plain, (![C_52, A_53, B_54]: (v4_relat_1(C_52, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.73/1.38  tff(c_138, plain, (![C_52, A_3]: (v4_relat_1(C_52, A_3) | ~m1_subset_1(C_52, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_132])).
% 2.73/1.38  tff(c_463, plain, (![C_108, A_109]: (v4_relat_1(C_108, A_109) | ~m1_subset_1(C_108, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_357, c_138])).
% 2.73/1.38  tff(c_470, plain, (![A_110]: (v4_relat_1('#skF_4', A_110))), inference(resolution, [status(thm)], [c_381, c_463])).
% 2.73/1.38  tff(c_18, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.73/1.38  tff(c_473, plain, (![A_110]: (k7_relat_1('#skF_4', A_110)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_470, c_18])).
% 2.73/1.38  tff(c_476, plain, (![A_110]: (k7_relat_1('#skF_4', A_110)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_473])).
% 2.73/1.38  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.73/1.38  tff(c_241, plain, (![A_83, B_84, C_85, D_86]: (k2_partfun1(A_83, B_84, C_85, D_86)=k7_relat_1(C_85, D_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_1(C_85))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.73/1.38  tff(c_245, plain, (![D_86]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_86)=k7_relat_1('#skF_4', D_86) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_241])).
% 2.73/1.38  tff(c_255, plain, (![D_86]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_86)=k7_relat_1('#skF_4', D_86))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_245])).
% 2.73/1.38  tff(c_46, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.73/1.38  tff(c_256, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_255, c_46])).
% 2.73/1.38  tff(c_479, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_476, c_256])).
% 2.73/1.38  tff(c_485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_479])).
% 2.73/1.38  tff(c_487, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_309])).
% 2.73/1.38  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.73/1.38  tff(c_166, plain, (![A_66, B_67, C_68]: (k1_relset_1(A_66, B_67, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.73/1.38  tff(c_176, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_166])).
% 2.73/1.38  tff(c_493, plain, (![B_114, A_115, C_116]: (k1_xboole_0=B_114 | k1_relset_1(A_115, B_114, C_116)=A_115 | ~v1_funct_2(C_116, A_115, B_114) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.73/1.38  tff(c_502, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_493])).
% 2.73/1.38  tff(c_515, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_176, c_502])).
% 2.73/1.38  tff(c_516, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_487, c_515])).
% 2.73/1.38  tff(c_194, plain, (![B_81]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_81, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_81))), inference(resolution, [status(thm)], [c_50, c_185])).
% 2.73/1.38  tff(c_22, plain, (![C_14, A_12, B_13]: (v4_relat_1(C_14, A_12) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.73/1.38  tff(c_218, plain, (![B_81]: (v4_relat_1('#skF_4', B_81) | ~r1_tarski(k1_relat_1('#skF_4'), B_81))), inference(resolution, [status(thm)], [c_194, c_22])).
% 2.73/1.38  tff(c_594, plain, (![B_118]: (v4_relat_1('#skF_4', B_118) | ~r1_tarski('#skF_1', B_118))), inference(demodulation, [status(thm), theory('equality')], [c_516, c_218])).
% 2.73/1.38  tff(c_597, plain, (![B_118]: (k7_relat_1('#skF_4', B_118)='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_1', B_118))), inference(resolution, [status(thm)], [c_594, c_18])).
% 2.73/1.38  tff(c_601, plain, (![B_119]: (k7_relat_1('#skF_4', B_119)='#skF_4' | ~r1_tarski('#skF_1', B_119))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_597])).
% 2.73/1.38  tff(c_611, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_48, c_601])).
% 2.73/1.38  tff(c_612, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_611, c_256])).
% 2.73/1.38  tff(c_615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_612])).
% 2.73/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.38  
% 2.73/1.38  Inference rules
% 2.73/1.38  ----------------------
% 2.73/1.38  #Ref     : 0
% 2.73/1.38  #Sup     : 124
% 2.73/1.38  #Fact    : 0
% 2.73/1.38  #Define  : 0
% 2.73/1.38  #Split   : 4
% 2.73/1.38  #Chain   : 0
% 2.73/1.38  #Close   : 0
% 2.73/1.38  
% 2.73/1.38  Ordering : KBO
% 2.73/1.38  
% 2.73/1.38  Simplification rules
% 2.73/1.38  ----------------------
% 2.73/1.38  #Subsume      : 12
% 2.73/1.38  #Demod        : 108
% 2.73/1.38  #Tautology    : 63
% 2.73/1.38  #SimpNegUnit  : 4
% 2.73/1.38  #BackRed      : 38
% 2.73/1.38  
% 2.73/1.38  #Partial instantiations: 0
% 2.73/1.38  #Strategies tried      : 1
% 2.73/1.38  
% 2.73/1.38  Timing (in seconds)
% 2.73/1.38  ----------------------
% 2.96/1.39  Preprocessing        : 0.33
% 2.96/1.39  Parsing              : 0.18
% 2.96/1.39  CNF conversion       : 0.02
% 2.96/1.39  Main loop            : 0.30
% 2.96/1.39  Inferencing          : 0.10
% 2.96/1.39  Reduction            : 0.10
% 2.96/1.39  Demodulation         : 0.07
% 2.96/1.39  BG Simplification    : 0.02
% 2.96/1.39  Subsumption          : 0.06
% 2.96/1.39  Abstraction          : 0.02
% 2.96/1.39  MUC search           : 0.00
% 2.96/1.39  Cooper               : 0.00
% 2.96/1.39  Total                : 0.66
% 2.96/1.39  Index Insertion      : 0.00
% 2.96/1.39  Index Deletion       : 0.00
% 2.96/1.39  Index Matching       : 0.00
% 2.96/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
