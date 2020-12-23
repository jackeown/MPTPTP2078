%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:06 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 458 expanded)
%              Number of leaves         :   30 ( 170 expanded)
%              Depth                    :   12
%              Number of atoms          :   90 ( 812 expanded)
%              Number of equality atoms :   42 ( 301 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_53,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_46])).

tff(c_83,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_53,c_83])).

tff(c_110,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(B_37,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_110])).

tff(c_119,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_112])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_140,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_16])).

tff(c_363,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( k8_relset_1(A_83,B_84,C_85,D_86) = k10_relat_1(C_85,D_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_374,plain,(
    ! [A_83,B_84,D_86] : k8_relset_1(A_83,B_84,'#skF_3',D_86) = k10_relat_1('#skF_3',D_86) ),
    inference(resolution,[status(thm)],[c_140,c_363])).

tff(c_233,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_248,plain,(
    ! [A_58,B_59] : k1_relset_1(A_58,B_59,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_140,c_233])).

tff(c_36,plain,(
    ! [C_24,B_23] :
      ( v1_funct_2(C_24,k1_xboole_0,B_23)
      | k1_relset_1(k1_xboole_0,B_23,C_24) != k1_xboole_0
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_55,plain,(
    ! [C_24,B_23] :
      ( v1_funct_2(C_24,k1_xboole_0,B_23)
      | k1_relset_1(k1_xboole_0,B_23,C_24) != k1_xboole_0
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_36])).

tff(c_251,plain,(
    ! [C_61,B_62] :
      ( v1_funct_2(C_61,'#skF_3',B_62)
      | k1_relset_1('#skF_3',B_62,C_61) != '#skF_3'
      | ~ m1_subset_1(C_61,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_119,c_119,c_119,c_55])).

tff(c_258,plain,(
    ! [B_62] :
      ( v1_funct_2('#skF_3','#skF_3',B_62)
      | k1_relset_1('#skF_3',B_62,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_140,c_251])).

tff(c_267,plain,(
    ! [B_62] :
      ( v1_funct_2('#skF_3','#skF_3',B_62)
      | k1_relat_1('#skF_3') != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_258])).

tff(c_268,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_48,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_139,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_48])).

tff(c_40,plain,(
    ! [B_23,C_24] :
      ( k1_relset_1(k1_xboole_0,B_23,C_24) = k1_xboole_0
      | ~ v1_funct_2(C_24,k1_xboole_0,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_54,plain,(
    ! [B_23,C_24] :
      ( k1_relset_1(k1_xboole_0,B_23,C_24) = k1_xboole_0
      | ~ v1_funct_2(C_24,k1_xboole_0,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_324,plain,(
    ! [B_78,C_79] :
      ( k1_relset_1('#skF_3',B_78,C_79) = '#skF_3'
      | ~ v1_funct_2(C_79,'#skF_3',B_78)
      | ~ m1_subset_1(C_79,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_119,c_119,c_119,c_54])).

tff(c_329,plain,
    ( k1_relset_1('#skF_3','#skF_1','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_139,c_324])).

tff(c_337,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_248,c_329])).

tff(c_339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_268,c_337])).

tff(c_341,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_342,plain,(
    ! [A_58,B_59] : k1_relset_1(A_58,B_59,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_248])).

tff(c_538,plain,(
    ! [A_121,B_122,C_123] :
      ( k8_relset_1(A_121,B_122,C_123,B_122) = k1_relset_1(A_121,B_122,C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_541,plain,(
    ! [A_121,B_122] : k8_relset_1(A_121,B_122,'#skF_3',B_122) = k1_relset_1(A_121,B_122,'#skF_3') ),
    inference(resolution,[status(thm)],[c_140,c_538])).

tff(c_550,plain,(
    ! [B_122] : k10_relat_1('#skF_3',B_122) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_342,c_541])).

tff(c_44,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_138,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_119,c_44])).

tff(c_376,plain,(
    k10_relat_1('#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_138])).

tff(c_555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:06:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.36  
% 2.20/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.36  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.20/1.36  
% 2.20/1.36  %Foreground sorts:
% 2.20/1.36  
% 2.20/1.36  
% 2.20/1.36  %Background operators:
% 2.20/1.36  
% 2.20/1.36  
% 2.20/1.36  %Foreground operators:
% 2.20/1.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.20/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.20/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.36  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.20/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.36  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.20/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.20/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.20/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.36  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.20/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.20/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.20/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.36  
% 2.64/1.38  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.64/1.38  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.64/1.38  tff(f_92, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.64/1.38  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.64/1.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.64/1.38  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.64/1.38  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.64/1.38  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.64/1.38  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.64/1.38  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.64/1.38  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.64/1.38  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.64/1.38  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.64/1.38  tff(c_53, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_46])).
% 2.64/1.38  tff(c_83, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | ~m1_subset_1(A_30, k1_zfmisc_1(B_31)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.64/1.38  tff(c_92, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_53, c_83])).
% 2.64/1.38  tff(c_110, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(B_37, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.38  tff(c_112, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_92, c_110])).
% 2.64/1.38  tff(c_119, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_112])).
% 2.64/1.38  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.64/1.38  tff(c_140, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_16])).
% 2.64/1.38  tff(c_363, plain, (![A_83, B_84, C_85, D_86]: (k8_relset_1(A_83, B_84, C_85, D_86)=k10_relat_1(C_85, D_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.64/1.38  tff(c_374, plain, (![A_83, B_84, D_86]: (k8_relset_1(A_83, B_84, '#skF_3', D_86)=k10_relat_1('#skF_3', D_86))), inference(resolution, [status(thm)], [c_140, c_363])).
% 2.64/1.38  tff(c_233, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.64/1.38  tff(c_248, plain, (![A_58, B_59]: (k1_relset_1(A_58, B_59, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_140, c_233])).
% 2.64/1.38  tff(c_36, plain, (![C_24, B_23]: (v1_funct_2(C_24, k1_xboole_0, B_23) | k1_relset_1(k1_xboole_0, B_23, C_24)!=k1_xboole_0 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.64/1.38  tff(c_55, plain, (![C_24, B_23]: (v1_funct_2(C_24, k1_xboole_0, B_23) | k1_relset_1(k1_xboole_0, B_23, C_24)!=k1_xboole_0 | ~m1_subset_1(C_24, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_36])).
% 2.64/1.38  tff(c_251, plain, (![C_61, B_62]: (v1_funct_2(C_61, '#skF_3', B_62) | k1_relset_1('#skF_3', B_62, C_61)!='#skF_3' | ~m1_subset_1(C_61, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_119, c_119, c_119, c_55])).
% 2.64/1.38  tff(c_258, plain, (![B_62]: (v1_funct_2('#skF_3', '#skF_3', B_62) | k1_relset_1('#skF_3', B_62, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_140, c_251])).
% 2.64/1.38  tff(c_267, plain, (![B_62]: (v1_funct_2('#skF_3', '#skF_3', B_62) | k1_relat_1('#skF_3')!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_248, c_258])).
% 2.64/1.38  tff(c_268, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(splitLeft, [status(thm)], [c_267])).
% 2.64/1.38  tff(c_48, plain, (v1_funct_2('#skF_3', k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.64/1.38  tff(c_139, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_48])).
% 2.64/1.38  tff(c_40, plain, (![B_23, C_24]: (k1_relset_1(k1_xboole_0, B_23, C_24)=k1_xboole_0 | ~v1_funct_2(C_24, k1_xboole_0, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.64/1.38  tff(c_54, plain, (![B_23, C_24]: (k1_relset_1(k1_xboole_0, B_23, C_24)=k1_xboole_0 | ~v1_funct_2(C_24, k1_xboole_0, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 2.64/1.38  tff(c_324, plain, (![B_78, C_79]: (k1_relset_1('#skF_3', B_78, C_79)='#skF_3' | ~v1_funct_2(C_79, '#skF_3', B_78) | ~m1_subset_1(C_79, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_119, c_119, c_119, c_54])).
% 2.64/1.38  tff(c_329, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_139, c_324])).
% 2.64/1.38  tff(c_337, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_248, c_329])).
% 2.64/1.38  tff(c_339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_268, c_337])).
% 2.64/1.38  tff(c_341, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_267])).
% 2.64/1.38  tff(c_342, plain, (![A_58, B_59]: (k1_relset_1(A_58, B_59, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_341, c_248])).
% 2.64/1.38  tff(c_538, plain, (![A_121, B_122, C_123]: (k8_relset_1(A_121, B_122, C_123, B_122)=k1_relset_1(A_121, B_122, C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.64/1.38  tff(c_541, plain, (![A_121, B_122]: (k8_relset_1(A_121, B_122, '#skF_3', B_122)=k1_relset_1(A_121, B_122, '#skF_3'))), inference(resolution, [status(thm)], [c_140, c_538])).
% 2.64/1.38  tff(c_550, plain, (![B_122]: (k10_relat_1('#skF_3', B_122)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_374, c_342, c_541])).
% 2.64/1.38  tff(c_44, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.64/1.38  tff(c_138, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_119, c_44])).
% 2.64/1.38  tff(c_376, plain, (k10_relat_1('#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_374, c_138])).
% 2.64/1.38  tff(c_555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_550, c_376])).
% 2.64/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.38  
% 2.64/1.38  Inference rules
% 2.64/1.38  ----------------------
% 2.64/1.38  #Ref     : 0
% 2.64/1.38  #Sup     : 104
% 2.64/1.38  #Fact    : 0
% 2.64/1.38  #Define  : 0
% 2.64/1.38  #Split   : 1
% 2.64/1.38  #Chain   : 0
% 2.64/1.38  #Close   : 0
% 2.64/1.38  
% 2.64/1.38  Ordering : KBO
% 2.64/1.38  
% 2.64/1.38  Simplification rules
% 2.64/1.38  ----------------------
% 2.64/1.38  #Subsume      : 7
% 2.64/1.38  #Demod        : 97
% 2.64/1.38  #Tautology    : 66
% 2.64/1.38  #SimpNegUnit  : 2
% 2.64/1.38  #BackRed      : 15
% 2.64/1.38  
% 2.64/1.38  #Partial instantiations: 0
% 2.64/1.38  #Strategies tried      : 1
% 2.64/1.38  
% 2.64/1.38  Timing (in seconds)
% 2.64/1.38  ----------------------
% 2.64/1.38  Preprocessing        : 0.32
% 2.64/1.38  Parsing              : 0.17
% 2.64/1.38  CNF conversion       : 0.02
% 2.64/1.38  Main loop            : 0.27
% 2.64/1.38  Inferencing          : 0.09
% 2.64/1.38  Reduction            : 0.09
% 2.64/1.38  Demodulation         : 0.06
% 2.64/1.38  BG Simplification    : 0.02
% 2.64/1.39  Subsumption          : 0.05
% 2.64/1.39  Abstraction          : 0.02
% 2.64/1.39  MUC search           : 0.00
% 2.64/1.39  Cooper               : 0.00
% 2.64/1.39  Total                : 0.63
% 2.64/1.39  Index Insertion      : 0.00
% 2.64/1.39  Index Deletion       : 0.00
% 2.64/1.39  Index Matching       : 0.00
% 2.64/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
