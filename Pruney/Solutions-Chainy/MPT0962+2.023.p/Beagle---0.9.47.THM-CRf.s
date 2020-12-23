%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:54 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 122 expanded)
%              Number of leaves         :   29 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :  126 ( 314 expanded)
%              Number of equality atoms :   27 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_75,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_48,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_818,plain,(
    ! [C_210,A_211,B_212] :
      ( m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212)))
      | ~ r1_tarski(k2_relat_1(C_210),B_212)
      | ~ r1_tarski(k1_relat_1(C_210),A_211)
      | ~ v1_relat_1(C_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42])).

tff(c_71,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_281,plain,(
    ! [C_84,A_85,B_86] :
      ( m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ r1_tarski(k2_relat_1(C_84),B_86)
      | ~ r1_tarski(k1_relat_1(C_84),A_85)
      | ~ v1_relat_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_12,B_13,C_14] :
      ( k1_relset_1(A_12,B_13,C_14) = k1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_306,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ r1_tarski(k2_relat_1(C_89),B_88)
      | ~ r1_tarski(k1_relat_1(C_89),A_87)
      | ~ v1_relat_1(C_89) ) ),
    inference(resolution,[status(thm)],[c_281,c_20])).

tff(c_311,plain,(
    ! [A_87] :
      ( k1_relset_1(A_87,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_87)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_306])).

tff(c_320,plain,(
    ! [A_90] :
      ( k1_relset_1(A_90,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_311])).

tff(c_330,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_320])).

tff(c_60,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_2'(A_28,B_29),A_28)
      | r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_28,B_29] :
      ( ~ v1_xboole_0(A_28)
      | r1_tarski(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_73,plain,(
    ! [B_32,A_33] :
      ( B_32 = A_33
      | ~ r1_tarski(B_32,A_33)
      | ~ r1_tarski(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_73])).

tff(c_86,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_86])).

tff(c_22,plain,(
    ! [C_17,A_15,B_16] :
      ( m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ r1_tarski(k2_relat_1(C_17),B_16)
      | ~ r1_tarski(k1_relat_1(C_17),A_15)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_384,plain,(
    ! [B_107,C_108,A_109] :
      ( k1_xboole_0 = B_107
      | v1_funct_2(C_108,A_109,B_107)
      | k1_relset_1(A_109,B_107,C_108) != A_109
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_489,plain,(
    ! [B_139,C_140,A_141] :
      ( k1_xboole_0 = B_139
      | v1_funct_2(C_140,A_141,B_139)
      | k1_relset_1(A_141,B_139,C_140) != A_141
      | ~ r1_tarski(k2_relat_1(C_140),B_139)
      | ~ r1_tarski(k1_relat_1(C_140),A_141)
      | ~ v1_relat_1(C_140) ) ),
    inference(resolution,[status(thm)],[c_22,c_384])).

tff(c_494,plain,(
    ! [A_141] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_141,'#skF_3')
      | k1_relset_1(A_141,'#skF_3','#skF_4') != A_141
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_141)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_489])).

tff(c_501,plain,(
    ! [A_141] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_141,'#skF_3')
      | k1_relset_1(A_141,'#skF_3','#skF_4') != A_141
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_494])).

tff(c_503,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_501])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_526,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_12])).

tff(c_528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_526])).

tff(c_531,plain,(
    ! [A_142] :
      ( v1_funct_2('#skF_4',A_142,'#skF_3')
      | k1_relset_1(A_142,'#skF_3','#skF_4') != A_142
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_142) ) ),
    inference(splitRight,[status(thm)],[c_501])).

tff(c_539,plain,
    ( v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_531])).

tff(c_543,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_539])).

tff(c_545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_543])).

tff(c_546,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_599,plain,(
    ! [A_155] :
      ( v1_funct_2(A_155,k1_relat_1(A_155),k2_relat_1(A_155))
      | ~ v1_funct_1(A_155)
      | ~ v1_relat_1(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_602,plain,
    ( v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_599])).

tff(c_604,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_602])).

tff(c_606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_604])).

tff(c_607,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_840,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_818,c_607])).

tff(c_849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_18,c_44,c_840])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:25:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.58  
% 3.21/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.59  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.21/1.59  
% 3.21/1.59  %Foreground sorts:
% 3.21/1.59  
% 3.21/1.59  
% 3.21/1.59  %Background operators:
% 3.21/1.59  
% 3.21/1.59  
% 3.21/1.59  %Foreground operators:
% 3.21/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.21/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.21/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.21/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.21/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.21/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.21/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.21/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.21/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.21/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.21/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.21/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.21/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.21/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.59  
% 3.21/1.60  tff(f_98, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.21/1.60  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.21/1.60  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.21/1.60  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.21/1.60  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.21/1.60  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.21/1.60  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.21/1.60  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.21/1.60  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 3.21/1.60  tff(c_48, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.21/1.60  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.21/1.60  tff(c_44, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.21/1.60  tff(c_818, plain, (![C_210, A_211, B_212]: (m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))) | ~r1_tarski(k2_relat_1(C_210), B_212) | ~r1_tarski(k1_relat_1(C_210), A_211) | ~v1_relat_1(C_210))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.21/1.60  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.21/1.60  tff(c_42, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.21/1.60  tff(c_50, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42])).
% 3.21/1.60  tff(c_71, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 3.21/1.60  tff(c_281, plain, (![C_84, A_85, B_86]: (m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~r1_tarski(k2_relat_1(C_84), B_86) | ~r1_tarski(k1_relat_1(C_84), A_85) | ~v1_relat_1(C_84))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.21/1.60  tff(c_20, plain, (![A_12, B_13, C_14]: (k1_relset_1(A_12, B_13, C_14)=k1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.21/1.60  tff(c_306, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~r1_tarski(k2_relat_1(C_89), B_88) | ~r1_tarski(k1_relat_1(C_89), A_87) | ~v1_relat_1(C_89))), inference(resolution, [status(thm)], [c_281, c_20])).
% 3.21/1.60  tff(c_311, plain, (![A_87]: (k1_relset_1(A_87, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), A_87) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_306])).
% 3.21/1.60  tff(c_320, plain, (![A_90]: (k1_relset_1(A_90, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), A_90))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_311])).
% 3.21/1.60  tff(c_330, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_320])).
% 3.21/1.60  tff(c_60, plain, (![A_28, B_29]: (r2_hidden('#skF_2'(A_28, B_29), A_28) | r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.21/1.60  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.60  tff(c_70, plain, (![A_28, B_29]: (~v1_xboole_0(A_28) | r1_tarski(A_28, B_29))), inference(resolution, [status(thm)], [c_60, c_2])).
% 3.21/1.60  tff(c_73, plain, (![B_32, A_33]: (B_32=A_33 | ~r1_tarski(B_32, A_33) | ~r1_tarski(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.21/1.60  tff(c_81, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_73])).
% 3.21/1.60  tff(c_86, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_81])).
% 3.21/1.60  tff(c_90, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_70, c_86])).
% 3.21/1.60  tff(c_22, plain, (![C_17, A_15, B_16]: (m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~r1_tarski(k2_relat_1(C_17), B_16) | ~r1_tarski(k1_relat_1(C_17), A_15) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.21/1.60  tff(c_384, plain, (![B_107, C_108, A_109]: (k1_xboole_0=B_107 | v1_funct_2(C_108, A_109, B_107) | k1_relset_1(A_109, B_107, C_108)!=A_109 | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_107))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.21/1.60  tff(c_489, plain, (![B_139, C_140, A_141]: (k1_xboole_0=B_139 | v1_funct_2(C_140, A_141, B_139) | k1_relset_1(A_141, B_139, C_140)!=A_141 | ~r1_tarski(k2_relat_1(C_140), B_139) | ~r1_tarski(k1_relat_1(C_140), A_141) | ~v1_relat_1(C_140))), inference(resolution, [status(thm)], [c_22, c_384])).
% 3.21/1.60  tff(c_494, plain, (![A_141]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_141, '#skF_3') | k1_relset_1(A_141, '#skF_3', '#skF_4')!=A_141 | ~r1_tarski(k1_relat_1('#skF_4'), A_141) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_489])).
% 3.21/1.60  tff(c_501, plain, (![A_141]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_141, '#skF_3') | k1_relset_1(A_141, '#skF_3', '#skF_4')!=A_141 | ~r1_tarski(k1_relat_1('#skF_4'), A_141))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_494])).
% 3.21/1.60  tff(c_503, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_501])).
% 3.21/1.60  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.21/1.60  tff(c_526, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_503, c_12])).
% 3.21/1.60  tff(c_528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_526])).
% 3.21/1.60  tff(c_531, plain, (![A_142]: (v1_funct_2('#skF_4', A_142, '#skF_3') | k1_relset_1(A_142, '#skF_3', '#skF_4')!=A_142 | ~r1_tarski(k1_relat_1('#skF_4'), A_142))), inference(splitRight, [status(thm)], [c_501])).
% 3.21/1.60  tff(c_539, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_531])).
% 3.21/1.60  tff(c_543, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_330, c_539])).
% 3.21/1.60  tff(c_545, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_543])).
% 3.21/1.60  tff(c_546, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_81])).
% 3.21/1.60  tff(c_599, plain, (![A_155]: (v1_funct_2(A_155, k1_relat_1(A_155), k2_relat_1(A_155)) | ~v1_funct_1(A_155) | ~v1_relat_1(A_155))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.21/1.60  tff(c_602, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_546, c_599])).
% 3.21/1.60  tff(c_604, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_602])).
% 3.21/1.60  tff(c_606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_604])).
% 3.21/1.60  tff(c_607, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(splitRight, [status(thm)], [c_50])).
% 3.21/1.60  tff(c_840, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_818, c_607])).
% 3.21/1.60  tff(c_849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_18, c_44, c_840])).
% 3.21/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.60  
% 3.21/1.60  Inference rules
% 3.21/1.60  ----------------------
% 3.21/1.60  #Ref     : 0
% 3.21/1.60  #Sup     : 164
% 3.21/1.60  #Fact    : 0
% 3.21/1.60  #Define  : 0
% 3.21/1.60  #Split   : 9
% 3.21/1.60  #Chain   : 0
% 3.21/1.60  #Close   : 0
% 3.21/1.60  
% 3.21/1.60  Ordering : KBO
% 3.21/1.60  
% 3.21/1.60  Simplification rules
% 3.21/1.60  ----------------------
% 3.21/1.60  #Subsume      : 47
% 3.21/1.60  #Demod        : 89
% 3.21/1.60  #Tautology    : 37
% 3.21/1.60  #SimpNegUnit  : 3
% 3.21/1.60  #BackRed      : 24
% 3.21/1.60  
% 3.21/1.60  #Partial instantiations: 0
% 3.21/1.60  #Strategies tried      : 1
% 3.21/1.60  
% 3.21/1.60  Timing (in seconds)
% 3.21/1.60  ----------------------
% 3.21/1.60  Preprocessing        : 0.37
% 3.21/1.60  Parsing              : 0.19
% 3.21/1.60  CNF conversion       : 0.02
% 3.21/1.60  Main loop            : 0.42
% 3.21/1.60  Inferencing          : 0.15
% 3.21/1.60  Reduction            : 0.11
% 3.21/1.60  Demodulation         : 0.07
% 3.21/1.60  BG Simplification    : 0.02
% 3.21/1.60  Subsumption          : 0.11
% 3.21/1.60  Abstraction          : 0.02
% 3.21/1.60  MUC search           : 0.00
% 3.21/1.60  Cooper               : 0.00
% 3.21/1.60  Total                : 0.82
% 3.21/1.60  Index Insertion      : 0.00
% 3.21/1.60  Index Deletion       : 0.00
% 3.21/1.60  Index Matching       : 0.00
% 3.21/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
