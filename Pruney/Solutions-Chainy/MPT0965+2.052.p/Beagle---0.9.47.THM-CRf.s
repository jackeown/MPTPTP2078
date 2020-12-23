%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:07 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 131 expanded)
%              Number of leaves         :   32 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  141 ( 301 expanded)
%              Number of equality atoms :   32 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
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

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_40,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_255,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_259,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_255])).

tff(c_397,plain,(
    ! [B_124,A_125,C_126] :
      ( k1_xboole_0 = B_124
      | k1_relset_1(A_125,B_124,C_126) = A_125
      | ~ v1_funct_2(C_126,A_125,B_124)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_404,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_397])).

tff(c_408,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_259,c_404])).

tff(c_409,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_408])).

tff(c_10,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_239,plain,(
    ! [B_79,A_80] :
      ( v1_relat_1(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_80))
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_242,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_239])).

tff(c_245,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_242])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_320,plain,(
    ! [B_99,A_100] :
      ( r2_hidden(k1_funct_1(B_99,A_100),k2_relat_1(B_99))
      | ~ r2_hidden(A_100,k1_relat_1(B_99))
      | ~ v1_funct_1(B_99)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_68,plain,(
    ! [A_42,B_43,C_44] :
      ( k1_relset_1(A_42,B_43,C_44) = k1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_72,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_68])).

tff(c_205,plain,(
    ! [B_75,A_76,C_77] :
      ( k1_xboole_0 = B_75
      | k1_relset_1(A_76,B_75,C_77) = A_76
      | ~ v1_funct_2(C_77,A_76,B_75)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_212,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_205])).

tff(c_216,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_72,c_212])).

tff(c_217,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_216])).

tff(c_50,plain,(
    ! [B_32,A_33] :
      ( v1_relat_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_53,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_50])).

tff(c_56,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_53])).

tff(c_12,plain,(
    ! [B_15,A_14] :
      ( r2_hidden(k1_funct_1(B_15,A_14),k2_relat_1(B_15))
      | ~ r2_hidden(A_14,k1_relat_1(B_15))
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_77,plain,(
    ! [A_45,B_46,C_47] :
      ( k2_relset_1(A_45,B_46,C_47) = k2_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_81,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_77])).

tff(c_86,plain,(
    ! [A_48,B_49,C_50] :
      ( m1_subset_1(k2_relset_1(A_48,B_49,C_50),k1_zfmisc_1(B_49))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_104,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_86])).

tff(c_111,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_104])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125,plain,(
    ! [A_53] :
      ( m1_subset_1(A_53,'#skF_2')
      | ~ r2_hidden(A_53,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_111,c_4])).

tff(c_129,plain,(
    ! [A_14] :
      ( m1_subset_1(k1_funct_1('#skF_4',A_14),'#skF_2')
      | ~ r2_hidden(A_14,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_125])).

tff(c_136,plain,(
    ! [A_14] :
      ( m1_subset_1(k1_funct_1('#skF_4',A_14),'#skF_2')
      | ~ r2_hidden(A_14,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_42,c_129])).

tff(c_229,plain,(
    ! [A_78] :
      ( m1_subset_1(k1_funct_1('#skF_4',A_78),'#skF_2')
      | ~ r2_hidden(A_78,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_136])).

tff(c_44,plain,(
    ! [A_30,B_31] :
      ( r2_hidden(A_30,B_31)
      | v1_xboole_0(B_31)
      | ~ m1_subset_1(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_48,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_32])).

tff(c_49,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_232,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_229,c_49])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_232])).

tff(c_237,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_266,plain,(
    ! [A_92,B_93,C_94] :
      ( k2_relset_1(A_92,B_93,C_94) = k2_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_270,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_266])).

tff(c_275,plain,(
    ! [A_95,B_96,C_97] :
      ( m1_subset_1(k2_relset_1(A_95,B_96,C_97),k1_zfmisc_1(B_96))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_293,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_275])).

tff(c_300,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_293])).

tff(c_6,plain,(
    ! [C_8,B_7,A_6] :
      ( ~ v1_xboole_0(C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_304,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_6,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_300,c_6])).

tff(c_311,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_304])).

tff(c_324,plain,(
    ! [A_100] :
      ( ~ r2_hidden(A_100,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_320,c_311])).

tff(c_327,plain,(
    ! [A_100] : ~ r2_hidden(A_100,k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_42,c_324])).

tff(c_411,plain,(
    ! [A_100] : ~ r2_hidden(A_100,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_327])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_411,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:02:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.34  
% 2.68/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.34  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.68/1.34  
% 2.68/1.34  %Foreground sorts:
% 2.68/1.34  
% 2.68/1.34  
% 2.68/1.34  %Background operators:
% 2.68/1.34  
% 2.68/1.34  
% 2.68/1.34  %Foreground operators:
% 2.68/1.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.68/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.68/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.68/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.68/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.68/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.68/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.68/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.68/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.34  
% 2.68/1.36  tff(f_104, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.68/1.36  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.68/1.36  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.68/1.36  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.68/1.36  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.68/1.36  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 2.68/1.36  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.68/1.36  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.68/1.36  tff(f_37, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.68/1.36  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.68/1.36  tff(f_44, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.68/1.36  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.68/1.36  tff(c_40, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.68/1.36  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.68/1.36  tff(c_255, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.68/1.36  tff(c_259, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_255])).
% 2.68/1.36  tff(c_397, plain, (![B_124, A_125, C_126]: (k1_xboole_0=B_124 | k1_relset_1(A_125, B_124, C_126)=A_125 | ~v1_funct_2(C_126, A_125, B_124) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.68/1.36  tff(c_404, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_397])).
% 2.68/1.36  tff(c_408, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_259, c_404])).
% 2.68/1.36  tff(c_409, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_34, c_408])).
% 2.68/1.36  tff(c_10, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.68/1.36  tff(c_239, plain, (![B_79, A_80]: (v1_relat_1(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_80)) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.68/1.36  tff(c_242, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_239])).
% 2.68/1.36  tff(c_245, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_242])).
% 2.68/1.36  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.68/1.36  tff(c_320, plain, (![B_99, A_100]: (r2_hidden(k1_funct_1(B_99, A_100), k2_relat_1(B_99)) | ~r2_hidden(A_100, k1_relat_1(B_99)) | ~v1_funct_1(B_99) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.68/1.36  tff(c_36, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.68/1.36  tff(c_68, plain, (![A_42, B_43, C_44]: (k1_relset_1(A_42, B_43, C_44)=k1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.68/1.36  tff(c_72, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_68])).
% 2.68/1.36  tff(c_205, plain, (![B_75, A_76, C_77]: (k1_xboole_0=B_75 | k1_relset_1(A_76, B_75, C_77)=A_76 | ~v1_funct_2(C_77, A_76, B_75) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.68/1.36  tff(c_212, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_205])).
% 2.68/1.36  tff(c_216, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_72, c_212])).
% 2.68/1.36  tff(c_217, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_34, c_216])).
% 2.68/1.36  tff(c_50, plain, (![B_32, A_33]: (v1_relat_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.68/1.36  tff(c_53, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_50])).
% 2.68/1.36  tff(c_56, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_53])).
% 2.68/1.36  tff(c_12, plain, (![B_15, A_14]: (r2_hidden(k1_funct_1(B_15, A_14), k2_relat_1(B_15)) | ~r2_hidden(A_14, k1_relat_1(B_15)) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.68/1.36  tff(c_77, plain, (![A_45, B_46, C_47]: (k2_relset_1(A_45, B_46, C_47)=k2_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.68/1.36  tff(c_81, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_77])).
% 2.68/1.36  tff(c_86, plain, (![A_48, B_49, C_50]: (m1_subset_1(k2_relset_1(A_48, B_49, C_50), k1_zfmisc_1(B_49)) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.68/1.36  tff(c_104, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_81, c_86])).
% 2.68/1.36  tff(c_111, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_104])).
% 2.68/1.36  tff(c_4, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.68/1.36  tff(c_125, plain, (![A_53]: (m1_subset_1(A_53, '#skF_2') | ~r2_hidden(A_53, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_111, c_4])).
% 2.68/1.36  tff(c_129, plain, (![A_14]: (m1_subset_1(k1_funct_1('#skF_4', A_14), '#skF_2') | ~r2_hidden(A_14, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_125])).
% 2.68/1.36  tff(c_136, plain, (![A_14]: (m1_subset_1(k1_funct_1('#skF_4', A_14), '#skF_2') | ~r2_hidden(A_14, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_42, c_129])).
% 2.68/1.36  tff(c_229, plain, (![A_78]: (m1_subset_1(k1_funct_1('#skF_4', A_78), '#skF_2') | ~r2_hidden(A_78, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_136])).
% 2.68/1.36  tff(c_44, plain, (![A_30, B_31]: (r2_hidden(A_30, B_31) | v1_xboole_0(B_31) | ~m1_subset_1(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.68/1.36  tff(c_32, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.68/1.36  tff(c_48, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_44, c_32])).
% 2.68/1.36  tff(c_49, plain, (~m1_subset_1(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 2.68/1.36  tff(c_232, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_229, c_49])).
% 2.68/1.36  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_232])).
% 2.68/1.36  tff(c_237, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 2.68/1.36  tff(c_266, plain, (![A_92, B_93, C_94]: (k2_relset_1(A_92, B_93, C_94)=k2_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.68/1.36  tff(c_270, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_266])).
% 2.68/1.36  tff(c_275, plain, (![A_95, B_96, C_97]: (m1_subset_1(k2_relset_1(A_95, B_96, C_97), k1_zfmisc_1(B_96)) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.68/1.36  tff(c_293, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_270, c_275])).
% 2.68/1.36  tff(c_300, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_293])).
% 2.68/1.36  tff(c_6, plain, (![C_8, B_7, A_6]: (~v1_xboole_0(C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.68/1.36  tff(c_304, plain, (![A_6]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_6, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_300, c_6])).
% 2.68/1.36  tff(c_311, plain, (![A_6]: (~r2_hidden(A_6, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_304])).
% 2.68/1.36  tff(c_324, plain, (![A_100]: (~r2_hidden(A_100, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_320, c_311])).
% 2.68/1.36  tff(c_327, plain, (![A_100]: (~r2_hidden(A_100, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_245, c_42, c_324])).
% 2.68/1.36  tff(c_411, plain, (![A_100]: (~r2_hidden(A_100, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_409, c_327])).
% 2.68/1.36  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_411, c_36])).
% 2.68/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.36  
% 2.68/1.36  Inference rules
% 2.68/1.36  ----------------------
% 2.68/1.36  #Ref     : 0
% 2.68/1.36  #Sup     : 76
% 2.68/1.36  #Fact    : 0
% 2.68/1.36  #Define  : 0
% 2.68/1.36  #Split   : 10
% 2.68/1.36  #Chain   : 0
% 2.68/1.36  #Close   : 0
% 2.68/1.36  
% 2.68/1.36  Ordering : KBO
% 2.68/1.36  
% 2.68/1.36  Simplification rules
% 2.68/1.36  ----------------------
% 2.68/1.36  #Subsume      : 7
% 2.68/1.36  #Demod        : 31
% 2.68/1.36  #Tautology    : 16
% 2.68/1.36  #SimpNegUnit  : 5
% 2.68/1.36  #BackRed      : 7
% 2.68/1.36  
% 2.68/1.36  #Partial instantiations: 0
% 2.68/1.36  #Strategies tried      : 1
% 2.68/1.36  
% 2.68/1.36  Timing (in seconds)
% 2.68/1.36  ----------------------
% 2.68/1.36  Preprocessing        : 0.33
% 2.68/1.36  Parsing              : 0.17
% 2.68/1.36  CNF conversion       : 0.02
% 2.68/1.36  Main loop            : 0.28
% 2.68/1.36  Inferencing          : 0.11
% 2.68/1.36  Reduction            : 0.08
% 2.68/1.36  Demodulation         : 0.05
% 2.68/1.36  BG Simplification    : 0.02
% 2.68/1.36  Subsumption          : 0.05
% 2.68/1.36  Abstraction          : 0.01
% 2.68/1.36  MUC search           : 0.00
% 2.68/1.36  Cooper               : 0.00
% 2.68/1.36  Total                : 0.65
% 2.68/1.36  Index Insertion      : 0.00
% 2.68/1.36  Index Deletion       : 0.00
% 2.68/1.36  Index Matching       : 0.00
% 2.68/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
