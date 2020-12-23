%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:02 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 107 expanded)
%              Number of leaves         :   35 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  119 ( 238 expanded)
%              Number of equality atoms :   27 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(c_56,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_65,plain,(
    ! [B_40,A_41] :
      ( ~ r2_hidden(B_40,A_41)
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_65])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_163,plain,(
    ! [C_67,B_68,A_69] :
      ( v5_relat_1(C_67,B_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_172,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_163])).

tff(c_22,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_110,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_116,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_110])).

tff(c_120,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_116])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_227,plain,(
    ! [A_92,B_93,C_94] :
      ( k1_relset_1(A_92,B_93,C_94) = k1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_236,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_227])).

tff(c_381,plain,(
    ! [B_126,A_127,C_128] :
      ( k1_xboole_0 = B_126
      | k1_relset_1(A_127,B_126,C_128) = A_127
      | ~ v1_funct_2(C_128,A_127,B_126)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_391,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_381])).

tff(c_396,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_236,c_391])).

tff(c_397,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_396])).

tff(c_24,plain,(
    ! [C_22,B_21,A_20] :
      ( m1_subset_1(k1_funct_1(C_22,B_21),A_20)
      | ~ r2_hidden(B_21,k1_relat_1(C_22))
      | ~ v1_funct_1(C_22)
      | ~ v5_relat_1(C_22,A_20)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_401,plain,(
    ! [B_21,A_20] :
      ( m1_subset_1(k1_funct_1('#skF_5',B_21),A_20)
      | ~ r2_hidden(B_21,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_20)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_24])).

tff(c_559,plain,(
    ! [B_132,A_133] :
      ( m1_subset_1(k1_funct_1('#skF_5',B_132),A_133)
      | ~ r2_hidden(B_132,'#skF_2')
      | ~ v5_relat_1('#skF_5',A_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_62,c_401])).

tff(c_94,plain,(
    ! [A_49,B_50] :
      ( r2_hidden(A_49,B_50)
      | v1_xboole_0(B_50)
      | ~ m1_subset_1(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_52,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_101,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_52])).

tff(c_109,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_602,plain,
    ( ~ r2_hidden('#skF_4','#skF_2')
    | ~ v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_559,c_109])).

tff(c_624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_56,c_602])).

tff(c_625,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_702,plain,(
    ! [C_155,B_156,A_157] :
      ( v1_xboole_0(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(B_156,A_157)))
      | ~ v1_xboole_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_709,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_702])).

tff(c_713,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_709])).

tff(c_781,plain,(
    ! [A_175,B_176,C_177] :
      ( k1_relset_1(A_175,B_176,C_177) = k1_relat_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_794,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_781])).

tff(c_923,plain,(
    ! [B_210,A_211,C_212] :
      ( k1_xboole_0 = B_210
      | k1_relset_1(A_211,B_210,C_212) = A_211
      | ~ v1_funct_2(C_212,A_211,B_210)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_211,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_933,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_923])).

tff(c_938,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_794,c_933])).

tff(c_939,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_938])).

tff(c_20,plain,(
    ! [A_17] :
      ( v1_xboole_0(k1_relat_1(A_17))
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_964,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_939,c_20])).

tff(c_982,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_964])).

tff(c_984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_982])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:41:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.99  
% 4.09/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.99  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.09/1.99  
% 4.09/1.99  %Foreground sorts:
% 4.09/1.99  
% 4.09/1.99  
% 4.09/1.99  %Background operators:
% 4.09/1.99  
% 4.09/1.99  
% 4.09/1.99  %Foreground operators:
% 4.09/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.09/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.09/1.99  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.09/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.09/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.09/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.09/1.99  tff('#skF_5', type, '#skF_5': $i).
% 4.09/1.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.09/1.99  tff('#skF_2', type, '#skF_2': $i).
% 4.09/1.99  tff('#skF_3', type, '#skF_3': $i).
% 4.09/1.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.09/1.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.09/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.09/1.99  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.09/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.09/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.09/1.99  tff('#skF_4', type, '#skF_4': $i).
% 4.09/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.99  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.09/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.09/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.09/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.09/1.99  
% 4.09/2.02  tff(f_135, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 4.09/2.02  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.09/2.02  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.09/2.02  tff(f_67, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.09/2.02  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.09/2.02  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.09/2.02  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.09/2.02  tff(f_77, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 4.09/2.02  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.09/2.02  tff(f_90, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.09/2.02  tff(f_65, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 4.09/2.02  tff(c_56, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.09/2.02  tff(c_65, plain, (![B_40, A_41]: (~r2_hidden(B_40, A_41) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.09/2.02  tff(c_69, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_65])).
% 4.09/2.02  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.09/2.02  tff(c_163, plain, (![C_67, B_68, A_69]: (v5_relat_1(C_67, B_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.09/2.02  tff(c_172, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_163])).
% 4.09/2.02  tff(c_22, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.09/2.02  tff(c_110, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.09/2.02  tff(c_116, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_110])).
% 4.09/2.02  tff(c_120, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_116])).
% 4.09/2.02  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.09/2.02  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.09/2.02  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.09/2.02  tff(c_227, plain, (![A_92, B_93, C_94]: (k1_relset_1(A_92, B_93, C_94)=k1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.09/2.02  tff(c_236, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_227])).
% 4.09/2.02  tff(c_381, plain, (![B_126, A_127, C_128]: (k1_xboole_0=B_126 | k1_relset_1(A_127, B_126, C_128)=A_127 | ~v1_funct_2(C_128, A_127, B_126) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.09/2.02  tff(c_391, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_381])).
% 4.09/2.02  tff(c_396, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_236, c_391])).
% 4.09/2.02  tff(c_397, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_396])).
% 4.09/2.02  tff(c_24, plain, (![C_22, B_21, A_20]: (m1_subset_1(k1_funct_1(C_22, B_21), A_20) | ~r2_hidden(B_21, k1_relat_1(C_22)) | ~v1_funct_1(C_22) | ~v5_relat_1(C_22, A_20) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.09/2.02  tff(c_401, plain, (![B_21, A_20]: (m1_subset_1(k1_funct_1('#skF_5', B_21), A_20) | ~r2_hidden(B_21, '#skF_2') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_20) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_397, c_24])).
% 4.09/2.02  tff(c_559, plain, (![B_132, A_133]: (m1_subset_1(k1_funct_1('#skF_5', B_132), A_133) | ~r2_hidden(B_132, '#skF_2') | ~v5_relat_1('#skF_5', A_133))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_62, c_401])).
% 4.09/2.02  tff(c_94, plain, (![A_49, B_50]: (r2_hidden(A_49, B_50) | v1_xboole_0(B_50) | ~m1_subset_1(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.09/2.02  tff(c_52, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.09/2.02  tff(c_101, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_94, c_52])).
% 4.09/2.02  tff(c_109, plain, (~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_101])).
% 4.09/2.02  tff(c_602, plain, (~r2_hidden('#skF_4', '#skF_2') | ~v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_559, c_109])).
% 4.09/2.02  tff(c_624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_56, c_602])).
% 4.09/2.02  tff(c_625, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_101])).
% 4.09/2.02  tff(c_702, plain, (![C_155, B_156, A_157]: (v1_xboole_0(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(B_156, A_157))) | ~v1_xboole_0(A_157))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.09/2.02  tff(c_709, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_702])).
% 4.09/2.02  tff(c_713, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_625, c_709])).
% 4.09/2.02  tff(c_781, plain, (![A_175, B_176, C_177]: (k1_relset_1(A_175, B_176, C_177)=k1_relat_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.09/2.02  tff(c_794, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_781])).
% 4.09/2.02  tff(c_923, plain, (![B_210, A_211, C_212]: (k1_xboole_0=B_210 | k1_relset_1(A_211, B_210, C_212)=A_211 | ~v1_funct_2(C_212, A_211, B_210) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_211, B_210))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.09/2.02  tff(c_933, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_923])).
% 4.09/2.02  tff(c_938, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_794, c_933])).
% 4.09/2.02  tff(c_939, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_938])).
% 4.09/2.02  tff(c_20, plain, (![A_17]: (v1_xboole_0(k1_relat_1(A_17)) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.09/2.02  tff(c_964, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_939, c_20])).
% 4.09/2.02  tff(c_982, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_713, c_964])).
% 4.09/2.02  tff(c_984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_982])).
% 4.09/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/2.02  
% 4.09/2.02  Inference rules
% 4.09/2.02  ----------------------
% 4.09/2.02  #Ref     : 0
% 4.09/2.02  #Sup     : 182
% 4.09/2.02  #Fact    : 0
% 4.09/2.02  #Define  : 0
% 4.09/2.02  #Split   : 5
% 4.09/2.02  #Chain   : 0
% 4.09/2.02  #Close   : 0
% 4.09/2.02  
% 4.09/2.02  Ordering : KBO
% 4.09/2.02  
% 4.09/2.02  Simplification rules
% 4.09/2.02  ----------------------
% 4.09/2.02  #Subsume      : 21
% 4.09/2.02  #Demod        : 91
% 4.09/2.02  #Tautology    : 55
% 4.09/2.02  #SimpNegUnit  : 12
% 4.09/2.02  #BackRed      : 2
% 4.09/2.02  
% 4.09/2.02  #Partial instantiations: 0
% 4.09/2.02  #Strategies tried      : 1
% 4.09/2.02  
% 4.09/2.02  Timing (in seconds)
% 4.09/2.02  ----------------------
% 4.09/2.02  Preprocessing        : 0.54
% 4.09/2.03  Parsing              : 0.29
% 4.09/2.03  CNF conversion       : 0.04
% 4.09/2.03  Main loop            : 0.65
% 4.09/2.03  Inferencing          : 0.26
% 4.09/2.03  Reduction            : 0.19
% 4.09/2.03  Demodulation         : 0.13
% 4.09/2.03  BG Simplification    : 0.04
% 4.09/2.03  Subsumption          : 0.11
% 4.09/2.03  Abstraction          : 0.03
% 4.09/2.03  MUC search           : 0.00
% 4.09/2.03  Cooper               : 0.00
% 4.09/2.03  Total                : 1.25
% 4.09/2.03  Index Insertion      : 0.00
% 4.09/2.03  Index Deletion       : 0.00
% 4.09/2.03  Index Matching       : 0.00
% 4.09/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
